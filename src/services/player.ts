import {VoiceChannel} from 'discord.js';
import {Readable, Transform} from 'stream';
import hasha from 'hasha';
import {WriteStream} from 'fs-capacitor';
import ffmpeg from 'fluent-ffmpeg';
import shuffle from 'array-shuffle';
import {
  AudioPlayer,
  AudioPlayerState,
  AudioPlayerStatus, AudioResource,
  createAudioPlayer,
  createAudioResource, DiscordGatewayAdapterCreator,
  entersState,
  joinVoiceChannel,
  StreamType,
  VoiceConnection,
  VoiceConnectionStatus,
} from '@discordjs/voice';
import FileCacheProvider from './file-cache.js';
import {PlaybackAttemptTracker, type PlaybackAttemptContext, type PlaybackAttemptToken} from './playback-attempt.js';
import {
  DEFAULT_VOLUME,
  MediaSource,
  STATUS,
  type AgeRestrictedFallbackResolver,
  type PlayerEvents,
  type QueuedPlaylist,
  type QueuedSong,
  type SongMetadata,
} from './player-types.js';
import {destroyVoiceConnection, recoverVoiceConnection} from './voice-connection-recovery.js';
import debug from '../utils/debug.js';
import errorMsg from '../utils/error-msg.js';
import {getGuildSettings} from '../utils/get-guild-settings.js';
import {buildPlayingMessageEmbed} from '../utils/build-embed.js';
import {getYouTubeMediaSource, YtDlpMediaUnavailableError} from '../utils/yt-dlp.js';
import {Setting} from '@prisma/client';

export {DEFAULT_VOLUME, MediaSource, STATUS};
export type {AgeRestrictedFallbackResolver, PlayerEvents, QueuedPlaylist, QueuedSong, SongMetadata};

type PlayerPlaybackAttemptContext = PlaybackAttemptContext<QueuedSong, VoiceConnection>;

const YOUTUBE_403_RETRY_ATTEMPTS = [
  {playerClient: 'visionos', useCookies: false},
  {playerClient: 'android_vr', useCookies: false},
  {playerClient: 'web', useCookies: true},
] as const;

class FfmpegForbiddenError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'FfmpegForbiddenError';
  }
}

export class AllPlayerClientsExhaustedError extends Error {
  constructor(videoId: string) {
    super(`All YouTube player clients exhausted for ${videoId}.`);
    this.name = 'AllPlayerClientsExhaustedError';
  }
}

const summarizeFfmpegError = (detail: string): string => {
  const lines = detail
    .split(/\r?\n/u)
    .map(line => line.trim())
    .filter(Boolean);
  const diagnosticLines = lines.filter(line => (
    /(?:HTTP error|Server returned|Forbidden|Invalid data|Conversion failed)/iu.test(line)
  ));

  return (diagnosticLines.length > 0 ? diagnosticLines.slice(-3) : lines.slice(-1)).join(' | ');
};

const appendPlaybackBounds = (ffmpegInputOptions: string[], options: {seek?: number; to?: number}) => {
  if (options.seek) {
    ffmpegInputOptions.push('-ss', options.seek.toString());
  }

  if (options.to) {
    ffmpegInputOptions.push('-to', options.to.toString());
  }
};

export default class {
  public voiceConnection: VoiceConnection | null = null;
  public status = STATUS.PAUSED;
  public guildId: string;
  public loopCurrentSong = false;
  public loopCurrentQueue = false;
  private currentChannel: VoiceChannel | undefined;
  private queue: QueuedSong[] = [];
  private queuePosition = 0;
  private audioPlayer: AudioPlayer | null = null;
  private audioResource: AudioResource | null = null;
  private volume?: number;
  private defaultVolume: number = DEFAULT_VOLUME;
  private nowPlaying: QueuedSong | null = null;
  private currentQueueEntryVersion = 0;
  private nowPlayingQueueEntryVersion: number | null = null;
  private readonly playbackAttempts: PlaybackAttemptTracker<QueuedSong, VoiceConnection>;
  private readonly programmaticallyStoppedAudioPlayers = new WeakSet<AudioPlayer>();
  private playPositionInterval: NodeJS.Timeout | undefined;

  private positionInSeconds = 0;
  private readonly fileCache: FileCacheProvider;
  private readonly ageRestrictedFallbackResolver?: AgeRestrictedFallbackResolver;
  private disconnectTimer: NodeJS.Timeout | null = null;

  private readonly channelToSpeakingUsers: Map<string, Set<string>> = new Map();
  private volumeBeforeVoiceActivity?: number;
  private voiceActivityVolumeTarget?: number;
  private voiceActivitySessionGeneration = 0;
  private hasRegisteredVoiceActivityListener = false;

  constructor(fileCache: FileCacheProvider, guildId: string, ageRestrictedFallbackResolver?: AgeRestrictedFallbackResolver) {
    this.fileCache = fileCache;
    this.guildId = guildId;
    this.ageRestrictedFallbackResolver = ageRestrictedFallbackResolver;
    this.playbackAttempts = new PlaybackAttemptTracker(() => ({
      currentSong: this.getCurrent(),
      queueEntryVersion: this.getCurrentQueueEntryId(),
      currentConnection: this.voiceConnection,
    }));
  }

  async connect(channel: VoiceChannel): Promise<void> {
    if (this.voiceConnection) {
      this.disconnect();
    }

    // Always get freshest default volume setting value
    const settings = await getGuildSettings(this.guildId);
    const {defaultVolume = DEFAULT_VOLUME} = settings;
    this.defaultVolume = defaultVolume;

    const voiceConnection = joinVoiceChannel({
      channelId: channel.id,
      guildId: channel.guild.id,
      selfDeaf: false,
      adapterCreator: channel.guild.voiceAdapterCreator as DiscordGatewayAdapterCreator,
    });

    this.voiceConnection = voiceConnection;
    this.currentChannel = channel;
    this.hasRegisteredVoiceActivityListener = false;

    voiceConnection.on('error', error => {
      console.error(`Voice connection error for guild ${this.guildId}:`, error);
    });

    const guildSettings = await getGuildSettings(this.guildId);
    const stateTransitions = [voiceConnection.state.status];
    voiceConnection.on('stateChange', (oldState, newState) => {
      stateTransitions.push(newState.status);
      if (stateTransitions.length > 10) {
        stateTransitions.shift();
      }

      debug(`Voice connection state changed: ${oldState.status} -> ${newState.status}`);

      if (this.voiceConnection === voiceConnection
        && newState.status === VoiceConnectionStatus.Ready
        && !this.hasRegisteredVoiceActivityListener) {
        this.registerVoiceActivityListener(guildSettings);
        this.hasRegisteredVoiceActivityListener = true;
      }
    });

    voiceConnection.on(
      VoiceConnectionStatus.Disconnected,
      this.onVoiceConnectionDisconnect.bind(this, voiceConnection),
    );

    try {
      await this.waitForVoiceConnectionReady(voiceConnection);
    } catch {
      const {status} = voiceConnection.state;
      destroyVoiceConnection(voiceConnection);

      if (this.voiceConnection === voiceConnection) {
        this.voiceConnection = null;
      }

      throw new Error(`Failed to connect to the voice channel (last state: ${status}, rejoin attempts: ${voiceConnection.rejoinAttempts}, recent states: ${stateTransitions.join(' -> ')}).`);
    }
  }

  disconnect(): void {
    this.playbackAttempts.invalidate();
    this.voiceActivitySessionGeneration++;

    if (this.voiceConnection) {
      if (this.status === STATUS.PLAYING) {
        this.pause();
      }

      this.loopCurrentSong = false;
      destroyVoiceConnection(this.voiceConnection);
      this.stopAudioPlayer(true);

      this.voiceConnection = null;
      this.audioPlayer = null;
      this.audioResource = null;
      this.currentChannel = undefined;
      this.channelToSpeakingUsers.clear();
      this.volumeBeforeVoiceActivity = undefined;
      this.voiceActivityVolumeTarget = undefined;
      this.hasRegisteredVoiceActivityListener = false;
    }
  }

  async seek(positionSeconds: number): Promise<void> {
    const attempt = this.playbackAttempts.begin();
    await this.seekWithAttempt(positionSeconds, attempt);
  }

  async forwardSeek(positionSeconds: number): Promise<void> {
    return this.seek(this.positionInSeconds + positionSeconds);
  }

  getPosition(): number {
    return this.positionInSeconds;
  }

  async play(allowAgeRestrictedFallback = true): Promise<void> {
    const attempt = this.playbackAttempts.begin();
    await this.playWithAttempt(attempt, allowAgeRestrictedFallback);
  }

  pause(): void {
    if (this.status !== STATUS.PLAYING) {
      throw new Error('Not currently playing.');
    }

    this.playbackAttempts.invalidate();
    this.status = STATUS.PAUSED;

    if (this.audioPlayer) {
      this.audioPlayer.pause();
    }

    this.stopTrackingPosition();
  }

  async forward(skip: number): Promise<void> {
    const originalQueuePosition = this.queuePosition;
    const originalQueueEntryVersion = this.currentQueueEntryVersion;
    this.manualForward(skip);
    const destinationSong = this.getCurrent();
    const destinationQueueEntryVersion = this.currentQueueEntryVersion;
    let destinationPlayback: PlayerPlaybackAttemptContext | null = null;

    try {
      if (!destinationSong) {
        await this.finishQueue();
      } else if (this.status !== STATUS.PAUSED) {
        const playPromise = this.play();
        const destinationConnection = this.voiceConnection;
        if (destinationConnection && destinationSong && destinationQueueEntryVersion !== null) {
          destinationPlayback = this.playbackAttempts.capture(
            this.playbackAttempts.latest(),
            destinationSong,
            destinationQueueEntryVersion,
            destinationConnection,
          );
        }

        await playPromise;
      }
    } catch (error: unknown) {
      const failedTransitionStillOwnsDestination = this.getCurrent() === destinationSong
        && this.currentQueueEntryVersion === destinationQueueEntryVersion
        && (destinationPlayback === null || this.playbackAttempts.owns(destinationPlayback));
      if (failedTransitionStillOwnsDestination) {
        this.queuePosition = originalQueuePosition;
        this.currentQueueEntryVersion = originalQueueEntryVersion;
      }

      throw error;
    }
  }

  registerVoiceActivityListener(guildSettings: Setting) {
    const {turnDownVolumeWhenPeopleSpeak, turnDownVolumeWhenPeopleSpeakTarget} = guildSettings;
    const {voiceConnection, currentChannel} = this;
    if (!turnDownVolumeWhenPeopleSpeak || !voiceConnection || !currentChannel) {
      return;
    }

    const voiceActivitySessionGeneration = ++this.voiceActivitySessionGeneration;
    const isCurrentVoiceActivitySession = () => (
      voiceActivitySessionGeneration === this.voiceActivitySessionGeneration
      && voiceConnection === this.voiceConnection
      && currentChannel === this.currentChannel
    );

    voiceConnection.receiver.speaking.on('start', (userId: string) => {
      if (!isCurrentVoiceActivitySession()) {
        return;
      }

      const member = currentChannel.members.get(userId);
      const {id: channelId} = currentChannel;

      if (member) {
        if (!this.channelToSpeakingUsers.has(channelId)) {
          this.channelToSpeakingUsers.set(channelId, new Set());
        }

        this.channelToSpeakingUsers.get(channelId)?.add(member.id);
      }

      this.suppressVoiceWhenPeopleAreSpeaking(turnDownVolumeWhenPeopleSpeakTarget);
    });

    voiceConnection.receiver.speaking.on('end', (userId: string) => {
      if (!isCurrentVoiceActivitySession()) {
        return;
      }

      this.channelToSpeakingUsers.get(currentChannel.id)?.delete(userId);

      this.suppressVoiceWhenPeopleAreSpeaking(turnDownVolumeWhenPeopleSpeakTarget);
    });
  }

  suppressVoiceWhenPeopleAreSpeaking(turnDownVolumeWhenPeopleSpeakTarget: number): void {
    if (!this.currentChannel) {
      return;
    }

    const speakingUsers = this.channelToSpeakingUsers.get(this.currentChannel.id);
    if (speakingUsers && speakingUsers.size > 0) {
      if (this.volumeBeforeVoiceActivity === undefined) {
        this.volumeBeforeVoiceActivity = this.getVolume();
      }

      this.voiceActivityVolumeTarget = turnDownVolumeWhenPeopleSpeakTarget;
      this.setAudioPlayerVolume(turnDownVolumeWhenPeopleSpeakTarget);
    } else if (this.volumeBeforeVoiceActivity !== undefined) {
      const {volumeBeforeVoiceActivity} = this;
      this.volumeBeforeVoiceActivity = undefined;
      this.voiceActivityVolumeTarget = undefined;
      this.setAudioPlayerVolume(volumeBeforeVoiceActivity);
    }
  }

  canGoForward(skip: number) {
    return (this.queuePosition + skip - 1) < this.queue.length;
  }

  manualForward(skip: number): void {
    if (this.canGoForward(skip)) {
      this.queuePosition += skip;
      this.currentQueueEntryVersion++;
      this.positionInSeconds = 0;
      this.stopTrackingPosition();
    } else {
      throw new Error('No songs in queue to forward to.');
    }
  }

  canGoBack() {
    return this.queuePosition - 1 >= 0;
  }

  async back(): Promise<void> {
    if (this.canGoBack()) {
      this.queuePosition--;
      this.currentQueueEntryVersion++;
      this.positionInSeconds = 0;
      this.stopTrackingPosition();

      if (this.status !== STATUS.PAUSED) {
        await this.play();
      }
    } else {
      throw new Error('No songs in queue to go back to.');
    }
  }

  getCurrent(): QueuedSong | null {
    if (this.queue[this.queuePosition]) {
      return this.queue[this.queuePosition];
    }

    return null;
  }

  getCurrentQueueEntryId(): number | null {
    return this.getCurrent() === null ? null : this.currentQueueEntryVersion;
  }

  /**
   * Returns queue, not including the current song.
   * @returns {QueuedSong[]}
   */
  getQueue(): QueuedSong[] {
    return this.queue.slice(this.queuePosition + 1);
  }

  add(song: QueuedSong, {immediate = false, immediateOffset = 0} = {}): void {
    const currentSong = this.getCurrent();

    if (immediate) {
      // Add as the next song to be played
      const insertAt = this.queuePosition + immediateOffset + 1;
      this.queue = [...this.queue.slice(0, insertAt), song, ...this.queue.slice(insertAt)];
    } else {
      // Add to end of queue
      this.queue.push(song);
    }

    if (this.getCurrent() !== currentSong) {
      this.currentQueueEntryVersion++;
    }
  }

  shuffle(): void {
    const shuffledSongs = shuffle(this.queue.slice(this.queuePosition + 1));

    this.queue = [...this.queue.slice(0, this.queuePosition + 1), ...shuffledSongs];
  }

  clear(): void {
    const newQueue = [];

    // Don't clear curently playing song
    const current = this.getCurrent();

    if (current) {
      newQueue.push(current);
    }

    this.queuePosition = 0;
    this.queue = newQueue;
  }

  removeFromQueue(index: number, amount = 1): void {
    this.queue.splice(this.queuePosition + index, amount);
  }

  removeCurrent(): void {
    this.queue = [...this.queue.slice(0, this.queuePosition), ...this.queue.slice(this.queuePosition + 1)];
    this.currentQueueEntryVersion++;
  }

  queueSize(): number {
    return this.getQueue().length;
  }

  isQueueEmpty(): boolean {
    return this.queueSize() === 0;
  }

  stop(): void {
    this.disconnect();
    this.queuePosition = 0;
    this.queue = [];
    this.currentQueueEntryVersion++;
  }

  move(from: number, to: number): QueuedSong {
    if (from > this.queueSize() || to > this.queueSize()) {
      throw new Error('Move index is outside the range of the queue.');
    }

    this.queue.splice(this.queuePosition + to, 0, this.queue.splice(this.queuePosition + from, 1)[0]);

    return this.queue[this.queuePosition + to];
  }

  setVolume(level: number): void {
    // Level should be a number between 0 and 100 = 0% => 100%
    this.volume = level;

    if (this.volumeBeforeVoiceActivity === undefined) {
      this.setAudioPlayerVolume(level);
    } else {
      this.volumeBeforeVoiceActivity = level;
      this.setAudioPlayerVolume(this.voiceActivityVolumeTarget);
    }
  }

  getVolume(): number {
    // Only use default volume if player volume is not already set (in the event of a reconnect we shouldn't reset)
    return this.voiceActivityVolumeTarget ?? this.volume ?? this.defaultVolume;
  }

  private async seekWithAttempt(positionSeconds: number, attempt: PlaybackAttemptToken): Promise<void> {
    this.status = STATUS.PAUSED;

    const currentSong = this.getCurrent();
    const currentQueueEntryVersion = this.getCurrentQueueEntryId();
    const voiceConnection = await this.ensureVoiceConnectionReady();

    if (!this.playbackAttempts.isCurrent(attempt, voiceConnection)) {
      return;
    }

    if (!currentSong) {
      throw new Error('No song currently playing');
    }

    if (currentQueueEntryVersion === null) {
      return;
    }

    const playback = this.playbackAttempts.capture(
      attempt,
      currentSong,
      currentQueueEntryVersion,
      voiceConnection,
    );
    if (!this.playbackAttempts.owns(playback)) {
      return;
    }

    if (positionSeconds > currentSong.length) {
      throw new Error('Seek position is outside the range of the song.');
    }

    let realPositionSeconds = positionSeconds;
    let to: number | undefined;
    if (currentSong.offset !== undefined) {
      realPositionSeconds += currentSong.offset;
      to = currentSong.length + currentSong.offset;
    }

    const stream = await this.getStream(currentSong, {seek: realPositionSeconds, to});
    if (!this.playbackAttempts.owns(playback)) {
      this.destroyStaleStream(stream);
      return;
    }

    this.audioPlayer = createAudioPlayer({
      behaviors: {
        // Needs to be somewhat high for livestreams
        maxMissedFrames: 50,
      },
    });
    voiceConnection.subscribe(this.audioPlayer);
    this.playAudioPlayerResource(this.createAudioStream(stream));
    this.attachListeners();
    this.startTrackingPosition(positionSeconds);

    this.status = STATUS.PLAYING;
    this.nowPlaying = currentSong;
    this.nowPlayingQueueEntryVersion = currentQueueEntryVersion;
  }

  private async playWithAttempt(attempt: PlaybackAttemptToken, allowAgeRestrictedFallback: boolean): Promise<void> {
    const currentSong = this.getCurrent();
    const currentQueueEntryVersion = this.getCurrentQueueEntryId();
    const voiceConnection = await this.ensureVoiceConnectionReady();

    if (!this.playbackAttempts.isCurrent(attempt, voiceConnection)) {
      return;
    }

    if (!currentSong) {
      throw new Error('Queue empty.');
    }

    if (currentQueueEntryVersion === null) {
      return;
    }

    const playback = this.playbackAttempts.capture(
      attempt,
      currentSong,
      currentQueueEntryVersion,
      voiceConnection,
    );
    if (!this.playbackAttempts.owns(playback)) {
      return;
    }

    // Cancel any pending idle disconnection
    if (this.disconnectTimer) {
      clearInterval(this.disconnectTimer);
      this.disconnectTimer = null;
    }

    // Resume from paused state
    if (this.status === STATUS.PAUSED
      && currentSong === this.nowPlaying
      && this.currentQueueEntryVersion === this.nowPlayingQueueEntryVersion) {
      if (this.audioPlayer) {
        this.audioPlayer.unpause();
        this.status = STATUS.PLAYING;
        this.startTrackingPosition();
        return;
      }

      // Was disconnected, need to recreate stream
      if (!currentSong.isLive) {
        return this.seekWithAttempt(this.getPosition(), attempt);
      }
    }

    try {
      let positionSeconds: number | undefined;
      let to: number | undefined;
      if (currentSong.offset !== undefined) {
        positionSeconds = currentSong.offset;
        to = currentSong.length + currentSong.offset;
      }

      const stream = await this.getStream(currentSong, {seek: positionSeconds, to});
      if (!this.playbackAttempts.owns(playback)) {
        this.destroyStaleStream(stream);
        return;
      }

      this.audioPlayer = createAudioPlayer({
        behaviors: {
          // Needs to be somewhat high for livestreams
          maxMissedFrames: 50,
        },
      });
      voiceConnection.subscribe(this.audioPlayer);
      this.playAudioPlayerResource(this.createAudioStream(stream));

      this.attachListeners();

      this.status = STATUS.PLAYING;
      this.nowPlaying = currentSong;
      this.nowPlayingQueueEntryVersion = currentQueueEntryVersion;
      this.startTrackingPosition(0);
    } catch (error: unknown) {
      await this.handlePlaybackError(
        error,
        playback,
        allowAgeRestrictedFallback,
      );
    }
  }

  private async handlePlaybackError(
    error: unknown,
    playback: PlayerPlaybackAttemptContext,
    allowAgeRestrictedFallback: boolean,
  ): Promise<void> {
    if (!this.playbackAttempts.owns(playback)) {
      throw error;
    }

    const isGone = typeof error === 'object'
      && error !== null
      && 'statusCode' in error
      && error.statusCode === 410;

    if (error instanceof AllPlayerClientsExhaustedError) {
      console.warn(`All YouTube player clients exhausted for guild ${this.guildId}; skipping ${playback.song.url}.`);
      if (this.currentChannel) {
        try {
          await this.currentChannel.send(errorMsg('all player clients exhausted, skipping to next song'));
        } catch (notificationError: unknown) {
          const detail = notificationError instanceof Error ? notificationError.message : String(notificationError);
          console.warn(`Could not announce exhausted YouTube player clients for guild ${this.guildId}: ${detail}`);
        }
      }

      await this.advancePastUnplayableTrack();
      return;
    }

    if (error instanceof YtDlpMediaUnavailableError
      && error.reason === 'age-restricted'
      && allowAgeRestrictedFallback) {
      const fallbackHandled = await this.tryAgeRestrictedAudioFallback(playback);
      if (fallbackHandled) {
        return;
      }

      if (!this.playbackAttempts.owns(playback)) {
        throw error;
      }
    }

    if (error instanceof YtDlpMediaUnavailableError || isGone) {
      const detail = error instanceof Error ? error.message : 'media returned HTTP 410';
      console.warn(`Skipping unplayable YouTube track for guild ${this.guildId}: ${detail}`);
      await this.advancePastUnplayableTrack();
      return;
    }

    throw error;
  }

  private getHashForCache(url: string): string {
    return hasha(url);
  }

  private async getStream(song: QueuedSong, options: {seek?: number; to?: number} = {}): Promise<Readable> {
    if (this.status === STATUS.PLAYING) {
      this.stopAudioPlayer();
    } else if (this.status === STATUS.PAUSED) {
      this.stopAudioPlayer(true);
    }

    if (song.source === MediaSource.HLS) {
      return this.createReadStream({url: song.url, cacheKey: song.url});
    }

    const cachedInput = await this.fileCache.getPathFor(this.getHashForCache(song.url));
    if (cachedInput) {
      const cachedInputOptions: string[] = [];
      appendPlaybackBounds(cachedInputOptions, options);

      return this.createReadStream({
        url: cachedInput,
        cacheKey: song.url,
        ffmpegInputOptions: cachedInputOptions,
      });
    }

    const extractionAttempts: ReadonlyArray<{playerClient?: string; useCookies: boolean}> = [
      {useCookies: true},
      ...YOUTUBE_403_RETRY_ATTEMPTS,
    ];
    let retryingAfterForbidden = false;
    for (const [index, {playerClient, useCookies}] of extractionAttempts.entries()) {
      try {
        // eslint-disable-next-line no-await-in-loop
        const mediaSource = await getYouTubeMediaSource(song.url, {playerClient, useCookies});
        const ffmpegInputOptions = [
          '-reconnect',
          '1',
          '-reconnect_streamed',
          '1',
          '-reconnect_delay_max',
          '5',
          ...this.buildFfmpegHeaderOptions(mediaSource.headers),
        ];
        appendPlaybackBounds(ffmpegInputOptions, options);

        // Don't cache livestreams or long videos
        const MAX_CACHE_LENGTH_SECONDS = 30 * 60; // 30 minutes
        const shouldCacheVideo = !mediaSource.isLive
          && song.length < MAX_CACHE_LENGTH_SECONDS
          && !options.seek;
        debug(`${shouldCacheVideo ? 'Caching' : 'Not caching'} video using ${playerClient ?? 'default'} client`);

        // Waiting here lets a pre-audio ffmpeg 403 trigger the next client instead of
        // being mistaken for a naturally completed Discord audio resource.
        // eslint-disable-next-line no-await-in-loop
        const stream = await this.createReadStream({
          url: mediaSource.url,
          cacheKey: song.url,
          ffmpegInputOptions,
          cache: shouldCacheVideo,
        });
        return stream;
      } catch (error: unknown) {
        const nextClient = extractionAttempts[index + 1]?.playerClient;
        const isForbidden = error instanceof FfmpegForbiddenError;
        retryingAfterForbidden ||= isForbidden;
        if (!retryingAfterForbidden) {
          throw error;
        }

        if (!nextClient) {
          throw new AllPlayerClientsExhaustedError(song.url);
        }

        console.warn(
          `${isForbidden ? 'ffmpeg received HTTP 403' : 'YouTube fallback failed'} for ${song.url} `
          + `using ${playerClient ?? 'default'} client; `
          + `retrying with ${nextClient}`,
        );
      }
    }

    throw new Error(`No playable YouTube media source found for ${song.url}.`);
  }

  private startTrackingPosition(initalPosition?: number): void {
    if (initalPosition !== undefined) {
      this.positionInSeconds = initalPosition;
    }

    if (this.playPositionInterval) {
      clearInterval(this.playPositionInterval);
    }

    this.playPositionInterval = setInterval(() => {
      this.positionInSeconds++;
    }, 1000);
  }

  private stopTrackingPosition(): void {
    if (this.playPositionInterval) {
      clearInterval(this.playPositionInterval);
      this.playPositionInterval = undefined;
    }
  }

  private attachListeners(): void {
    if (!this.voiceConnection) {
      return;
    }

    if (!this.audioPlayer) {
      return;
    }

    const {audioPlayer} = this;
    const queueEntryVersion = this.currentQueueEntryVersion;
    if (audioPlayer.listeners(AudioPlayerStatus.Idle).length === 0) {
      audioPlayer.on(AudioPlayerStatus.Idle, (oldState, newState) => {
        if (this.programmaticallyStoppedAudioPlayers.has(audioPlayer)
          || this.audioPlayer !== audioPlayer
          || this.currentQueueEntryVersion !== queueEntryVersion) {
          return;
        }

        void this.onAudioPlayerIdle(oldState, newState).catch(error => {
          console.error(`Audio player idle handler failed for guild ${this.guildId}:`, error);
        });
      });
    }
  }

  private async onVoiceConnectionDisconnect(voiceConnection: VoiceConnection): Promise<void> {
    await recoverVoiceConnection(voiceConnection, {
      isCurrent: candidate => this.voiceConnection === candidate,
      dispose: candidate => {
        if (this.voiceConnection === candidate) {
          this.disconnect();
        } else {
          destroyVoiceConnection(candidate);
        }
      },
    });
  }

  private async ensureVoiceConnectionReady(): Promise<VoiceConnection> {
    if (this.voiceConnection === null) {
      throw new Error('Not connected to a voice channel.');
    }

    await this.waitForVoiceConnectionReady(this.voiceConnection);

    return this.voiceConnection;
  }

  private async waitForVoiceConnectionReady(voiceConnection: VoiceConnection): Promise<void> {
    await entersState(voiceConnection, VoiceConnectionStatus.Ready, 60_000);
  }

  private async advancePastUnplayableTrack(): Promise<void> {
    this.manualForward(1);

    if (!this.getCurrent()) {
      await this.finishQueue();
      return;
    }

    await this.play();
  }

  private async tryAgeRestrictedAudioFallback(playback: PlayerPlaybackAttemptContext): Promise<boolean> {
    const {song, queueEntryVersion, attempt, connection} = playback;
    if (!this.ageRestrictedFallbackResolver || song.source !== MediaSource.Youtube) {
      return false;
    }

    if (!this.playbackAttempts.owns(playback)) {
      return true;
    }

    let fallback: SongMetadata | null;
    try {
      fallback = await this.ageRestrictedFallbackResolver(song);
    } catch {
      if (!this.playbackAttempts.owns(playback)) {
        return true;
      }

      console.warn(`Audio fallback search failed for age-restricted track in guild ${this.guildId}.`);
      return false;
    }

    if (!this.playbackAttempts.owns(playback)) {
      return true;
    }

    if (!fallback || fallback.source !== MediaSource.Youtube || fallback.url === song.url) {
      return false;
    }

    const {queuePosition} = this;
    const replacement: QueuedSong = {
      ...fallback,
      playlist: song.playlist,
      addedInChannelId: song.addedInChannelId,
      requestedBy: song.requestedBy,
    };
    this.queue[queuePosition] = replacement;
    const replacementPlayback = this.playbackAttempts.capture(
      attempt,
      replacement,
      queueEntryVersion,
      connection,
    );
    console.warn(`Trying audio fallback for age-restricted YouTube track in guild ${this.guildId}: ${song.url} -> ${replacement.url}`);

    try {
      await this.playWithAttempt(attempt, false);
      return true;
    } catch (error: unknown) {
      if (this.playbackAttempts.owns(replacementPlayback)
        && this.queue[queuePosition] === replacement) {
        this.queue[queuePosition] = song;
      }

      throw error;
    }
  }

  private async onAudioPlayerIdle(_oldState: AudioPlayerState, newState: AudioPlayerState): Promise<void> {
    const idleSong = this.getCurrent();
    if (newState.status === AudioPlayerStatus.Idle
      && idleSong
      && idleSong.length > 0
      && this.positionInSeconds + 2 < idleSong.length) {
      debug(
        `Audio player became idle early for ${idleSong.url} `
        + `at ${this.positionInSeconds}s (expected length: ${idleSong.length}s)`,
      );
    }

    // Automatically advance queued song at end
    if (this.loopCurrentSong && newState.status === AudioPlayerStatus.Idle && this.status === STATUS.PLAYING) {
      await this.seek(0);
      return;
    }

    // Automatically re-add current song to queue
    if (this.loopCurrentQueue && newState.status === AudioPlayerStatus.Idle && this.status === STATUS.PLAYING) {
      const currentSong = this.getCurrent();

      if (currentSong) {
        this.add(currentSong);
      } else {
        throw new Error('No song currently playing.');
      }
    }

    if (newState.status === AudioPlayerStatus.Idle && this.status === STATUS.PLAYING) {
      if (!this.canGoForward(1)) {
        await this.finishQueue();
        return;
      }

      await this.forward(1);
      const currentSong = this.getCurrent();
      if (!currentSong) {
        return;
      }

      // Auto announce the next song if configured to
      const settings = await getGuildSettings(this.guildId);
      const {autoAnnounceNextSong} = settings;
      if (autoAnnounceNextSong && this.currentChannel) {
        await this.currentChannel.send({
          embeds: [buildPlayingMessageEmbed(this)],
        });
      }
    }
  }

  private async finishQueue(): Promise<void> {
    this.playbackAttempts.invalidate();
    this.stopTrackingPosition();
    this.status = STATUS.IDLE;
    this.stopAudioPlayer(true);

    const settings = await getGuildSettings(this.guildId);

    const {secondsToWaitAfterQueueEmpties} = settings;
    if (secondsToWaitAfterQueueEmpties !== 0) {
      this.disconnectTimer = setTimeout(() => {
        // Make sure we are not accidentally playing
        // when disconnecting
        if (this.status === STATUS.IDLE) {
          this.disconnect();
        }
      }, secondsToWaitAfterQueueEmpties * 1000);
    }
  }

  private buildFfmpegHeaderOptions(headers: Record<string, string>) {
    const headerLines = Object.entries(headers)
      .map(([key, value]) => `${key}: ${value}`)
      .join('\r\n');

    if (!headerLines) {
      return [];
    }

    return ['-headers', `${headerLines}\r\n`];
  }

  private async createReadStream(options: {url: string; cacheKey: string; ffmpegInputOptions?: string[]; cache?: boolean}): Promise<Readable> {
    return new Promise((resolve, reject) => {
      const capacitor = new WriteStream();
      let ffmpegStderr = '';
      const maxFfmpegStderrCharacters = 32_768;
      let hasFfmpegOutput = false;
      let hasSettled = false;

      if (options?.cache) {
        const cacheStream = this.fileCache.createWriteStream(this.getHashForCache(options.cacheKey));
        capacitor.createReadStream().pipe(cacheStream);
      }

      const returnedStream = capacitor.createReadStream();
      let hasReturnedStreamClosed = false;
      const outputProbe = new Transform({
        transform(chunk, _encoding, callback) {
          if (!hasFfmpegOutput) {
            hasFfmpegOutput = true;
            hasSettled = true;
            resolve(returnedStream);
          }

          callback(null, chunk);
        },
      });
      outputProbe.pipe(capacitor);

      const stream = ffmpeg(options.url)
        .inputOptions(options?.ffmpegInputOptions ?? ['-re'])
        .noVideo()
        .audioCodec('libopus')
        .outputFormat('webm')
        .on('stderr', line => {
          ffmpegStderr = `${ffmpegStderr}${line}\n`.slice(-maxFfmpegStderrCharacters);
        })
        .on('error', (error, _stdout, stderr) => {
          const detail = (stderr || ffmpegStderr || error.message)
            .trim()
            .replace(/https?:\/\/\S*googlevideo\.com\/\S+/giu, '[redacted signed Google Video URL]');
          const summary = summarizeFfmpegError(detail);
          console.error(`ffmpeg playback failed for ${options.cacheKey}: ${summary}`);

          if (!hasFfmpegOutput && !hasSettled) {
            hasSettled = true;
            returnedStream.destroy();
            reject(/(?:HTTP error 403|403 Forbidden|Server returned 403)/iu.test(detail)
              ? new FfmpegForbiddenError(summary)
              : error);
          }
        })
        .on('end', () => {
          if (!hasFfmpegOutput && !hasSettled) {
            hasSettled = true;
            returnedStream.destroy();
            reject(new Error(`ffmpeg produced no audio output for ${options.cacheKey}.`));
          }
        });

      stream.pipe(outputProbe);

      returnedStream.on('close', () => {
        if (!options.cache) {
          stream.kill('SIGKILL');
        }

        hasReturnedStreamClosed = true;
      });
    });
  }

  private createAudioStream(stream: Readable) {
    return createAudioResource(stream, {
      inputType: StreamType.WebmOpus,
      inlineVolume: true,
    });
  }

  private playAudioPlayerResource(resource: AudioResource) {
    if (this.audioPlayer !== null) {
      this.audioResource = resource;
      this.setAudioPlayerVolume();
      this.audioPlayer.play(this.audioResource);
    }
  }

  private setAudioPlayerVolume(level?: number) {
    // Audio resource expects a float between 0 and 1 to represent level percentage
    this.audioResource?.volume?.setVolume((level ?? this.getVolume()) / 100);
  }

  private stopAudioPlayer(force = false): void {
    if (!this.audioPlayer) {
      return;
    }

    this.programmaticallyStoppedAudioPlayers.add(this.audioPlayer);
    this.audioPlayer.stop(force);
  }

  private destroyStaleStream(stream: Readable): void {
    if (!stream.destroyed) {
      stream.destroy();
    }
  }
}
