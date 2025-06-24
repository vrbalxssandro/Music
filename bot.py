import discord
from discord import app_commands
from discord.ext import commands, tasks
from discord.ui import View, Button
import asyncio
import yt_dlp
from yt_dlp import utils as yt_dlp_utils
import re
import json
import os
import datetime
from datetime import timezone, timedelta
from typing import Optional, Union, List, Dict, Any, Callable
import functools
import random
import aiohttp
import sys
import traceback
from io import StringIO # For queue export

# --- CONFIGURATION ---
BOT_TOKEN = os.getenv("DISCORD_BOT_TOKEN")
if not BOT_TOKEN:
    print("CRITICAL ERROR: DISCORD_BOT_TOKEN environment variable not set.")
    sys.exit(1)

GUILD_SETTINGS_DIR = "guild_music_settings"
USER_PLAYLISTS_DIR = "user_playlists"
CUSTOM_PREFIXES_FILE = "custom_prefixes.json"

AUTO_LEAVE_DELAY = 120  # seconds
MAX_QUEUE_SIZE = 250
MAX_SEARCH_RESULTS = 5 # For slash command AND text command search view
MAX_SEARCH_RESULTS_PER_ROW = 5 # For SearchResultsView button layout
UP_NEXT_NOTIFICATION_SECONDS = 15 # Increased slightly
VOTE_SKIP_PERCENTAGE = 0.5 # 50%

DEFAULT_FFMPEG_BEFORE_OPTIONS = '-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5 -nostdin'
DEFAULT_FFMPEG_OPTIONS_AUDIO_ONLY = '-vn'
LOUDNESS_NORMALIZATION_FILTER = 'loudnorm=I=-16:TP=-1.5:LRA=11'
DEFAULT_AUDIO_FILTERS = LOUDNESS_NORMALIZATION_FILTER

# --- DATA PERSISTENCE ---
if not os.path.exists(GUILD_SETTINGS_DIR): os.makedirs(GUILD_SETTINGS_DIR)
if not os.path.exists(USER_PLAYLISTS_DIR): os.makedirs(USER_PLAYLISTS_DIR)

# --- BOT SETUP ---
# --- BOT SETUP ---
class MyClient(commands.Bot):
    def __init__(self, *, intents: discord.Intents, command_prefix: Union[str, List[str], Callable]):
        super().__init__(command_prefix=command_prefix, intents=intents, help_command=None)
        self.start_time = datetime.datetime.now(timezone.utc)
        self._voice_clients: Dict[int, discord.VoiceClient] = {}
        self._queues: Dict[int, List[Dict[str, Any]]] = {}
        self._current_song: Dict[int, Optional[Dict[str, Any]]] = {}
        self._leave_tasks: Dict[int, asyncio.Task] = {}
        self._last_text_channel: Dict[int, discord.TextChannel] = {} # For updates and commands
        self._interactive_np_message_ids: Dict[int, int] = {} # guild_id -> message_id

        self._guild_settings: Dict[int, Dict[str, Any]] = {}

        self._session_controllers: Dict[int, List[int]] = {}
        self._original_joiner: Dict[int, int] = {}
        self._up_next_tasks: Dict[int, asyncio.Task] = {}
        self._is_processing_next_song: Dict[int, bool] = {}
        self._vote_skips: Dict[int, Dict[int, List[int]]] = {}

        self._pending_text_searches: Dict[int, Dict[str, Any]] = {}

        self.custom_prefixes: Dict[int, List[str]] = {}
        if callable(command_prefix):
            self.default_prefix_val = "m!"
        elif isinstance(command_prefix, list):
            self.default_prefix_val = command_prefix[0] if command_prefix else "m!"
        else:
            self.default_prefix_val = command_prefix

    # Guild Setting Accessors
    def get_guild_volume(self, guild_id: int) -> float: return self._guild_settings.get(guild_id, {}).get("volume", 0.5)
    def set_guild_volume(self, guild_id: int, volume: float):
        self._guild_settings.setdefault(guild_id, {})["volume"] = volume
        if guild_id in self._voice_clients and self._voice_clients[guild_id].source:
             if isinstance(self._voice_clients[guild_id].source, discord.PCMVolumeTransformer):
                self._voice_clients[guild_id].source.volume = volume

    def get_guild_loop_mode(self, guild_id: int) -> str: return self._guild_settings.get(guild_id, {}).get("loop_mode", "off")
    def set_guild_loop_mode(self, guild_id: int, mode: str): self._guild_settings.setdefault(guild_id, {})["loop_mode"] = mode

    def get_guild_ffmpeg_filters(self, guild_id: int) -> str: return self._guild_settings.get(guild_id, {}).get("ffmpeg_filters", DEFAULT_AUDIO_FILTERS)
    def set_guild_ffmpeg_filters(self, guild_id: int, filters: str): self._guild_settings.setdefault(guild_id, {})["ffmpeg_filters"] = filters

    def get_guild_smart_autoplay(self, guild_id: int) -> bool: return self._guild_settings.get(guild_id, {}).get("smart_autoplay", True)
    def set_guild_smart_autoplay(self, guild_id: int, enabled: bool): self._guild_settings.setdefault(guild_id, {})["smart_autoplay"] = enabled

    def get_guild_24_7_mode(self, guild_id: int) -> bool: return self._guild_settings.get(guild_id, {}).get("is_24_7_mode", False)
    def set_guild_24_7_mode(self, guild_id: int, enabled: bool): self._guild_settings.setdefault(guild_id, {})["is_24_7_mode"] = enabled

    def get_guild_autoplay_genre(self, guild_id: int) -> Optional[str]: return self._guild_settings.get(guild_id, {}).get("autoplay_genre", None)
    def set_guild_autoplay_genre(self, guild_id: int, genre: Optional[str]): self._guild_settings.setdefault(guild_id, {})["autoplay_genre"] = genre
        
    def get_last_known_vc_channel_id(self, guild_id: int) -> Optional[int]: return self._guild_settings.get(guild_id, {}).get("last_known_vc_channel_id", None)
    def set_last_known_vc_channel_id(self, guild_id: int, channel_id: Optional[int]): self._guild_settings.setdefault(guild_id, {})["last_known_vc_channel_id"] = channel_id

    def get_guild_dj_role_id(self, guild_id: int) -> Optional[int]: return self._guild_settings.get(guild_id, {}).get("dj_role_id", None)
    def set_guild_dj_role_id(self, guild_id: int, role_id: Optional[int]): self._guild_settings.setdefault(guild_id, {})["dj_role_id"] = role_id

    async def setup_hook(self):
        self.tree.add_command(music_group)
        await self.tree.sync()
        self.loop.create_task(self.load_all_guild_settings_on_startup()) # Call to method
        self.loop.create_task(self.load_custom_prefixes_from_file())
        self.loop.create_task(self.cleanup_old_pending_searches())
        self.loop.create_task(self.attempt_24_7_rejoins_on_startup()) # Call to method

    async def get_prefix(self, message: discord.Message):
        if not message.guild:
            return commands.when_mentioned_or(self.default_prefix_val)(self, message)
        guild_prefixes = self.custom_prefixes.get(message.guild.id, [self.default_prefix_val])
        return commands.when_mentioned_or(*guild_prefixes)(self, message)

    async def load_custom_prefixes_from_file(self):
        if os.path.exists(CUSTOM_PREFIXES_FILE):
            try:
                with open(CUSTOM_PREFIXES_FILE, "r") as f:
                    self.custom_prefixes = {int(k): v for k, v in json.load(f).items()}
            except Exception as e:
                print(f"Error loading custom prefixes: {e}")

    async def save_custom_prefixes_to_file(self):
        try:
            with open(CUSTOM_PREFIXES_FILE, "w") as f:
                json.dump(self.custom_prefixes, f, indent=4)
        except Exception as e:
            print(f"Error saving custom prefixes: {e}")

    def get_guild_settings_save_path(self, guild_id: int) -> str:
        return os.path.join(GUILD_SETTINGS_DIR, f"{guild_id}_settings.json")

    def get_user_playlist_path(self, user_id: int) -> str:
        return os.path.join(USER_PLAYLISTS_DIR, f"{user_id}_playlists.json")

    # These methods must be indented to be part of MyClient
    async def save_guild_settings_to_file(self, guild_id: int):
        settings_path = self.get_guild_settings_save_path(guild_id)
        queue_to_save_serializable = []
        original_queue = self._queues.get(guild_id, [])
        for song in original_queue:
            s_copy = song.copy()
            s_copy.pop('play_start_utc', None)
            queue_to_save_serializable.append(s_copy)

        current_playing_song_serializable = None
        current_playing_song_original = self._current_song.get(guild_id)
        if current_playing_song_original:
            current_playing_song_serializable = current_playing_song_original.copy()
            current_playing_song_serializable.pop('play_start_utc', None)
            if current_playing_song_original.get('play_start_utc'):
                elapsed_this_segment = (datetime.datetime.now(timezone.utc) - current_playing_song_original['play_start_utc']).total_seconds()
                current_playing_song_serializable['accumulated_play_time_seconds'] = \
                    current_playing_song_original.get('accumulated_play_time_seconds', 0.0) + elapsed_this_segment
            
            if not queue_to_save_serializable or \
               (queue_to_save_serializable[0].get('webpage_url') != current_playing_song_serializable.get('webpage_url')):
                queue_to_save_serializable.insert(0, current_playing_song_serializable)
        
        self._guild_settings.setdefault(guild_id, {})
        data_to_save = {
            "queue": queue_to_save_serializable,
            "volume": self.get_guild_volume(guild_id),
            "loop_mode": self.get_guild_loop_mode(guild_id),
            "ffmpeg_filters": self.get_guild_ffmpeg_filters(guild_id),
            "smart_autoplay": self.get_guild_smart_autoplay(guild_id),
            "is_24_7_mode": self.get_guild_24_7_mode(guild_id),
            "autoplay_genre": self.get_guild_autoplay_genre(guild_id),
            "last_known_vc_channel_id": self.get_last_known_vc_channel_id(guild_id),
            "dj_role_id": self.get_guild_dj_role_id(guild_id),
        }
        try:
            with open(settings_path, 'w') as f:
                json.dump(data_to_save, f, indent=4)
        except Exception as e:
            print(f"Error saving settings for guild {guild_id}: {e}")
            traceback.print_exc()

    async def load_guild_settings_from_file(self, guild_id: int):
        settings_path = self.get_guild_settings_save_path(guild_id)
        self._guild_settings[guild_id] = {
            "volume": 0.5, "loop_mode": "off", "ffmpeg_filters": DEFAULT_AUDIO_FILTERS,
            "smart_autoplay": True, "is_24_7_mode": False, "autoplay_genre": None,
            "last_known_vc_channel_id": None, "dj_role_id": None,
        }
        self._queues[guild_id] = []
        if os.path.exists(settings_path):
            try:
                with open(settings_path, 'r') as f: data = json.load(f)
                for key in self._guild_settings[guild_id].keys():
                    if key in data: self._guild_settings[guild_id][key] = data[key]
                self._queues[guild_id] = data.get("queue", [])
            except Exception as e:
                print(f"Error loading settings for guild {guild_id}: {e}. Using defaults.")
                self._queues[guild_id] = []
        self._session_controllers.pop(guild_id, None); self._original_joiner.pop(guild_id, None)
        self._current_song.pop(guild_id, None)

    async def load_all_guild_settings_on_startup(self): # Now correctly indented
        print("Loading saved guild settings...")
        for filename in os.listdir(GUILD_SETTINGS_DIR):
            if filename.endswith("_settings.json"):
                try:
                    guild_id_str = filename.split("_")[0]
                    if guild_id_str.isdigit(): await self.load_guild_settings_from_file(int(guild_id_str))
                except Exception as e: print(f"Error startup settings load for {filename}: {e}")
        print("Finished loading guild settings.")

    async def attempt_24_7_rejoins_on_startup(self): # Now correctly indented
        await self.wait_until_ready()
        print("Attempting 24/7 rejoins...")
        for guild_id_str_settings_file in os.listdir(GUILD_SETTINGS_DIR): # Renamed to avoid conflict
             if guild_id_str_settings_file.endswith("_settings.json"):
                try:
                    guild_id_str = guild_id_str_settings_file.split("_")[0]
                    if not guild_id_str.isdigit(): continue # Skip if filename isn't as expected
                    guild_id = int(guild_id_str)

                    # Ensure settings are loaded for this guild if not already
                    if guild_id not in self._guild_settings:
                        await self.load_guild_settings_from_file(guild_id)

                    if self.get_guild_24_7_mode(guild_id):
                        channel_id = self.get_last_known_vc_channel_id(guild_id)
                        guild = self.get_guild(guild_id)
                        if guild and channel_id:
                            vc_channel = guild.get_channel(channel_id)
                            if isinstance(vc_channel, discord.VoiceChannel):
                                try:
                                    print(f"Attempting 24/7 rejoin to {vc_channel.name} in {guild.name}")
                                    vc = await vc_channel.connect(timeout=10.0, reconnect=True)
                                    self._voice_clients[guild_id] = vc
                                    self._last_text_channel[guild_id] = guild.system_channel or next((tc for tc in guild.text_channels if tc.permissions_for(guild.me).send_messages), None)
                                    if self._queues.get(guild_id) and not vc.is_playing():
                                        await self._play_guild_queue(guild_id)
                                    elif not self._queues.get(guild_id) and self.get_guild_autoplay_genre(guild_id):
                                        await self._play_guild_queue(guild_id)
                                    print(f"Successfully rejoined {vc_channel.name} for 24/7 mode.")
                                except Exception as e: print(f"Failed 24/7 rejoin for guild {guild_id} to channel {channel_id}: {e}")
                            else: print(f"24/7 rejoin: VC ID {channel_id} not found or not a voice channel in guild {guild_id}.")
                except Exception as e_outer:
                    print(f"Error processing file {guild_id_str_settings_file} for 24/7 rejoin: {e_outer}")
        print("Finished 24/7 rejoin attempts.")

    def is_controller(self, interaction_or_ctx: Union[discord.Interaction, commands.Context]) -> bool:
        guild = interaction_or_ctx.guild
        user_obj_param = interaction_or_ctx.user if isinstance(interaction_or_ctx, discord.Interaction) else interaction_or_ctx.author
        
        if not guild or not user_obj_param: return False
        
        member_obj = None
        if isinstance(user_obj_param, discord.Member):
            member_obj = user_obj_param
        elif isinstance(user_obj_param, discord.User): # If it's a User, try to get Member
            member_obj = guild.get_member(user_obj_param.id)
        
        if not member_obj: return False # Cannot determine permissions without Member object

        guild_id = guild.id
        user_id = member_obj.id # Use ID from Member object

        if member_obj.guild_permissions.administrator: return True
        
        dj_role_id = self.get_guild_dj_role_id(guild_id)
        if dj_role_id and discord.utils.get(member_obj.roles, id=dj_role_id): return True

        if self._original_joiner.get(guild_id) == user_id: return True
        return user_id in self._session_controllers.get(guild_id, [])

    async def ensure_voice_client(self, interaction_or_ctx: Union[discord.Interaction, commands.Context, Any], join_if_not_connected: bool = True) -> Optional[discord.VoiceClient]: # Added Any for PseudoContext
        guild = interaction_or_ctx.guild; guild_id = guild.id
        author_param = interaction_or_ctx.user if isinstance(interaction_or_ctx, discord.Interaction) else interaction_or_ctx.author
        
        # Ensure author is a Member object to get voice state
        author_member = None
        if isinstance(interaction_or_ctx, discord.Interaction):
            guild = interaction_or_ctx.guild
            author_param = interaction_or_ctx.user
            text_channel_for_updates = interaction_or_ctx.channel
        elif isinstance(interaction_or_ctx, commands.Context):
            guild = interaction_or_ctx.guild
            author_param = interaction_or_ctx.author
            text_channel_for_updates = interaction_or_ctx.channel
        else: # Assuming PseudoContext or similar duck-typed object
            guild = interaction_or_ctx.guild
            author_param = interaction_or_ctx.author # or .user
            text_channel_for_updates = interaction_or_ctx.channel

        if not guild: # Should not happen if called from guild context
            print("ERROR: ensure_voice_client called without a guild.")
            return None

        author_member = None
        if isinstance(author_param, discord.Member):
            author_member = author_param
        elif isinstance(author_param, discord.User): # If it's a User, try to get Member
            author_member = guild.get_member(author_param.id)

        if not author_member:
             # For PseudoContext, send_custom_response won't work as it expects Interaction/Context
             # So, send directly to the text_channel_for_updates
             if text_channel_for_updates and isinstance(text_channel_for_updates, discord.TextChannel):
                 await text_channel_for_updates.send(embed=create_error_embed("Could not identify you as a member of this server (for voice operations)."))
             else: # Fallback print
                 print(f"ERROR: Could not identify user {author_param.id} as a member of guild {guild.id}.")
             return None

        text_channel_for_updates = interaction_or_ctx.channel
        user_vc_channel = author_member.voice.channel if author_member.voice else None
        current_vc = self._voice_clients.get(guild_id)

        if not user_vc_channel and join_if_not_connected:
            await send_custom_response(interaction_or_ctx, embed=create_error_embed("You need to be in a voice channel for me to join."), ephemeral_preference=None)
            return None

        if current_vc and current_vc.is_connected():
            if user_vc_channel and current_vc.channel != user_vc_channel:
                try: await current_vc.move_to(user_vc_channel)
                except asyncio.TimeoutError:
                    await send_custom_response(interaction_or_ctx, embed=create_error_embed("Timed out moving to your voice channel."), ephemeral_preference=None)
                    return None
                self.set_last_known_vc_channel_id(guild_id, user_vc_channel.id)
                await self.save_guild_settings_to_file(guild_id) # Corrected call
                if self._original_joiner.get(guild_id) == author_member.id:
                    self._session_controllers.setdefault(guild_id, []).clear(); self._session_controllers[guild_id].append(author_member.id)
        elif user_vc_channel and join_if_not_connected:
            try:
                if guild_id not in self._guild_settings: await self.load_guild_settings_from_file(guild_id) # Corrected call
                vc = await user_vc_channel.connect(timeout=10.0, reconnect=True)
                self._voice_clients[guild_id] = vc
                self.set_last_known_vc_channel_id(guild_id, user_vc_channel.id)
                await self.save_guild_settings_to_file(guild_id) # Corrected call
                if guild_id not in self._original_joiner or not self._session_controllers.get(guild_id):
                    self._original_joiner[guild_id] = author_member.id
                    self._session_controllers.setdefault(guild_id, []).clear(); self._session_controllers[guild_id].append(author_member.id)
            except Exception as e:
                err_msg_connect = f"Failed to connect: {e}"
                if isinstance(e, discord.opus.OpusNotLoaded): err_msg_connect = "Opus library not loaded. Please ensure libopus is installed."
                elif isinstance(e, asyncio.TimeoutError): err_msg_connect = "Timed out connecting to your voice channel."
                await send_custom_response(interaction_or_ctx, embed=create_error_embed(err_msg_connect), ephemeral_preference=None)
                return None
        elif not join_if_not_connected and not current_vc: return None

        if self._voice_clients.get(guild_id) and text_channel_for_updates and isinstance(text_channel_for_updates, discord.TextChannel):
            self._last_text_channel[guild_id] = text_channel_for_updates
        return self._voice_clients.get(guild_id)

    async def find_genre_stream(self, genre: str) -> Optional[Dict[str, Any]]:
        queries = [f"{genre} live stream music", f"{genre} 24/7 radio", f"{genre} mix playlist"]
        for query_str in queries:
            try:
                stream_info_result = await get_audio_stream_info(query_str, search=True, search_results_count=1)
                if stream_info_result and "error" not in stream_info_result and stream_info_result.get('webpage_url'):
                    is_live = stream_info_result.get('is_live', False)
                    duration = stream_info_result.get('duration')
                    if is_live or duration is None or (isinstance(duration, (int,float)) and duration > 3600 * 2):
                        final_stream_info = await get_audio_stream_info(stream_info_result['webpage_url'], search=False)
                        if final_stream_info and "error" not in final_stream_info and final_stream_info.get('url'):
                            return {'webpage_url': final_stream_info.get('webpage_url'), 'title': final_stream_info.get('title', f"{genre} Autoplay"),
                                    'duration': final_stream_info.get('duration'), 'thumbnail': final_stream_info.get('thumbnail'),
                                    'uploader': final_stream_info.get('uploader', "Autoplay Service"), 'requester': self.user.mention,
                                    'stream_url': final_stream_info.get('url'), 'is_live_stream': True }
            except Exception as e: print(f"Error in find_genre_stream for '{genre}' with query '{query_str}': {e}")
        return None

    async def _play_guild_queue(self, guild_id: int, song_to_replay: Optional[Dict[str, Any]] = None, seek_seconds: Optional[float] = None):
        print(f"\nDEBUG PLAY_QUEUE: Called for guild {guild_id}. Replay: {bool(song_to_replay)}, Seek: {seek_seconds}s") # Q1
        if guild_id in self._leave_tasks: self._leave_tasks[guild_id].cancel(); self._leave_tasks.pop(guild_id, None)
        if guild_id in self._up_next_tasks: self._up_next_tasks[guild_id].cancel(); self._up_next_tasks.pop(guild_id, None)
        
        # Check if already processing, to prevent race conditions if _handle_after_play calls this too quickly
        if self._is_processing_next_song.get(guild_id, False) and not song_to_replay and not seek_seconds:
             print(f"DEBUG PLAY_QUEUE: Already processing next song for guild {guild_id}. Aborting duplicate call.") # Q1.1
             return
        self._is_processing_next_song[guild_id] = True # Set flag early

        song_info = None
        guild_loop_mode = self.get_guild_loop_mode(guild_id)
        guild_is_24_7 = self.get_guild_24_7_mode(guild_id)
        guild_autoplay_genre = self.get_guild_autoplay_genre(guild_id)
        guild_smart_autoplay = self.get_guild_smart_autoplay(guild_id)
        current_queue = self._queues.get(guild_id, [])
        current_playing_song_before_pop = self._current_song.get(guild_id) # Song that was playing

        print(f"DEBUG PLAY_QUEUE: Guild {guild_id} - Loop: {guild_loop_mode}, 24/7: {guild_is_24_7}, AutoplayGenre: {guild_autoplay_genre}, SmartAutoplay: {guild_smart_autoplay}, Queue size before logic: {len(current_queue)}") # Q2

        if song_to_replay:
            song_info = song_to_replay
            print(f"DEBUG PLAY_QUEUE: Replaying song: {song_info.get('title')}") # Q3
        elif current_queue: # Check if self._queues[guild_id] exists and is not empty
            song_info = current_queue.pop(0) # Pop from the actual queue
            self._queues[guild_id] = current_queue # Update the queue in our client's state
            print(f"DEBUG PLAY_QUEUE: Popped from queue: {song_info.get('title')}. New queue size: {len(self._queues[guild_id])}") # Q4
            if guild_loop_mode == "queue" and current_playing_song_before_pop:
                 # Add the song that *just finished* (or was current) to the end of the queue
                 song_that_was_playing_copy = current_playing_song_before_pop.copy()
                 song_that_was_playing_copy.pop('play_start_utc', None) # Clear runtime state
                 song_that_was_playing_copy.pop('accumulated_play_time_seconds', None)
                 self._queues[guild_id].append(song_that_was_playing_copy)
                 print(f"DEBUG PLAY_QUEUE: Loop 'queue' active. Added '{song_that_was_playing_copy.get('title')}' back to queue. New size: {len(self._queues[guild_id])}") # Q5
        # ... (rest of your autoplay logic for 24/7 and smart autoplay - ensure these also correctly set song_info) ...
        elif guild_is_24_7 and guild_autoplay_genre:
            print(f"DEBUG PLAY_QUEUE: 24/7 mode with genre '{guild_autoplay_genre}'. Finding stream.") # Q6
            # ... (find_genre_stream logic) ...
            if self._last_text_channel.get(guild_id):
                try: await self._last_text_channel[guild_id].send(f"🎶 Queue ended. Autoplaying genre: **{guild_autoplay_genre}** (24/7 Mode)...")
                except discord.HTTPException: pass
            genre_song_info = await self.find_genre_stream(guild_autoplay_genre)
            if genre_song_info: song_info = genre_song_info
            else:
                if self._last_text_channel.get(guild_id):
                    try: await self._last_text_channel[guild_id].send(embed=create_error_embed(f"24/7 Autoplay: Could not find a stream for genre '{guild_autoplay_genre}'. Pausing."))
                    except discord.HTTPException: pass
                self._current_song[guild_id] = None; await self.save_guild_settings_to_file(guild_id)
                self._is_processing_next_song[guild_id] = False # Reset flag
                return
        elif guild_smart_autoplay and current_playing_song_before_pop and guild_loop_mode == "off":
            print(f"DEBUG PLAY_QUEUE: Smart autoplay based on '{current_playing_song_before_pop.get('title')}'.") # Q7
            # ... (smart autoplay logic) ...
            last_song = current_playing_song_before_pop
            autoplay_query = f"{last_song.get('title','')} {last_song.get('uploader','')}"
            if self._last_text_channel.get(guild_id):
                try: await self._last_text_channel[guild_id].send(f"🤖 Queue ended. Autoplaying related to: **{last_song.get('title')}**...")
                except discord.HTTPException: pass
            autoplay_info_result = await get_audio_stream_info(autoplay_query, search=True, search_results_count=1) # Ensure this returns a single item dict
            if autoplay_info_result and "error" not in autoplay_info_result and autoplay_info_result.get('webpage_url'):
                # If get_audio_stream_info returns the entry directly for search=True, count=1
                song_info = {'webpage_url': autoplay_info_result.get('webpage_url'), 'title': autoplay_info_result.get('title', 'Autoplay'),
                             'duration': autoplay_info_result.get('duration'), 'thumbnail': autoplay_info_result.get('thumbnail'),
                             'uploader': autoplay_info_result.get('uploader'), 'requester': self.user.mention, # Bot is requester for autoplay
                             'stream_url': autoplay_info_result.get('url')} # Crucial: make sure 'url' is present
            else:
                if self._last_text_channel.get(guild_id):
                    try: await self._last_text_channel[guild_id].send(embed=create_error_embed("Autoplay failed to find a related song."))
                    except discord.HTTPException: pass
                self._current_song[guild_id] = None; await self.save_guild_settings_to_file(guild_id)
                if self._voice_clients.get(guild_id) and not guild_is_24_7: await self.schedule_leave(guild_id)
                self._is_processing_next_song[guild_id] = False # Reset flag
                return
        else: # No song to play from queue, replay, or autoplay
            print(f"DEBUG PLAY_QUEUE: No song found in queue, no replay, no applicable autoplay. Stopping playback for guild {guild_id}.") # Q8
            self._current_song[guild_id] = None
            await self.save_guild_settings_to_file(guild_id)
            if self._voice_clients.get(guild_id) and not guild_is_24_7:
                await self.schedule_leave(guild_id)
            # Delete interactive NP message if queue ends
            if self._interactive_np_message_ids.get(guild_id) and self._last_text_channel.get(guild_id):
                try:
                    old_np_msg = await self._last_text_channel[guild_id].fetch_message(self._interactive_np_message_ids[guild_id])
                    await old_np_msg.delete()
                except (discord.NotFound, discord.HTTPException): pass
                self._interactive_np_message_ids.pop(guild_id, None)
            self._is_processing_next_song[guild_id] = False # Reset flag
            return

        vc = self._voice_clients.get(guild_id)
        if not vc or not vc.is_connected():
            print(f"DEBUG PLAY_QUEUE: VC not found or not connected for guild {guild_id} before playing. Aborting.") # Q9
            self._is_processing_next_song[guild_id] = False # Reset flag
            # Optionally try to put song_info back if it was popped
            if song_info and not song_to_replay and self._queues.get(guild_id) is not None : # if popped from queue
                 self._queues.setdefault(guild_id, []).insert(0, song_info)
            return
        
        # If VC is already playing something and this isn't a seek/replay, something is wrong (e.g. rapid fire after_play)
        # This check is now earlier with self._is_processing_next_song
        # if vc.is_playing() and not seek_seconds and not song_to_replay:
        # print(f"DEBUG PLAY_QUEUE: VC is already playing but not seek/replay for guild {guild_id}. This might be an issue.")
        # self._is_processing_next_song[guild_id] = False
        # return


        # --- Song Playback Setup ---
        self._current_song[guild_id] = song_info.copy() # Make a copy to avoid modifying original in queue
        self._current_song[guild_id]['play_start_utc'] = datetime.datetime.now(timezone.utc)
        self._current_song[guild_id]['accumulated_play_time_seconds'] = seek_seconds if seek_seconds else 0.0
        print(f"DEBUG PLAY_QUEUE: Set current_song for guild {guild_id}: {self._current_song[guild_id].get('title')} at {self._current_song[guild_id]['play_start_utc']}") # Q10
        await self.save_guild_settings_to_file(guild_id) # Save current song state

        # Delete previous interactive NP message
        if self._interactive_np_message_ids.get(guild_id) and self._last_text_channel.get(guild_id):
            try:
                old_np_msg = await self._last_text_channel[guild_id].fetch_message(self._interactive_np_message_ids[guild_id])
                await old_np_msg.delete()
            except (discord.NotFound, discord.HTTPException): pass
            self._interactive_np_message_ids.pop(guild_id, None)

        try:
            stream_data_url = song_info.get('stream_url')
            # If stream_url is missing (e.g. from saved queue or older addition), re-fetch it.
            if not stream_data_url:
                print(f"DEBUG PLAY_QUEUE: stream_url missing for '{song_info.get('title')}'. Re-fetching from webpage_url: {song_info.get('webpage_url')}") # Q11
                # Ensure webpage_url exists before trying to fetch
                if not song_info.get('webpage_url'):
                    err_msg_no_url = "Song has no webpage_url to fetch stream data from."
                    print(f"DEBUG PLAY_QUEUE: ERROR - {err_msg_no_url}")
                    if self._last_text_channel.get(guild_id):
                        await self._last_text_channel[guild_id].send(embed=create_error_embed(f"Skipping '{song_info.get('title', 'Unknown song')}': {err_msg_no_url}"))
                    self._is_processing_next_song[guild_id] = False # Reset before recursive call
                    await self._play_guild_queue(guild_id) # Try next song
                    return

                # Re-fetch full info to get a fresh stream URL
                fresh_stream_info = await get_audio_stream_info(song_info['webpage_url'], search=False)
                if not fresh_stream_info or "error" in fresh_stream_info or not fresh_stream_info.get('url'):
                    err_msg = fresh_stream_info['error'] if fresh_stream_info and 'error' in fresh_stream_info else "Could not get audio stream data after re-fetch."
                    print(f"DEBUG PLAY_QUEUE: Re-fetch failed for '{song_info.get('title')}'. Error: {err_msg}") # Q12
                    if self._last_text_channel.get(guild_id):
                        await self._last_text_channel[guild_id].send(embed=create_error_embed(f"Skipping '{song_info.get('title', 'Unknown song')}': {err_msg}"))
                    self._is_processing_next_song[guild_id] = False # Reset before recursive call
                    await self._play_guild_queue(guild_id) # Try next song
                    return
                stream_data_url = fresh_stream_info['url']
                self._current_song[guild_id]['stream_url'] = stream_data_url # Update current song with fresh URL
                # Also update other relevant fields from fresh_stream_info if they changed
                for key in ['title', 'duration', 'thumbnail', 'uploader']:
                    if fresh_stream_info.get(key) and self._current_song[guild_id].get(key) != fresh_stream_info.get(key):
                        self._current_song[guild_id][key] = fresh_stream_info.get(key)
                print(f"DEBUG PLAY_QUEUE: Successfully re-fetched stream_url: {stream_data_url[:60]}...")

            # ... (rest of FFmpeg options setup, source creation, vc.play call) ...
            ffmpeg_before_options_list = DEFAULT_FFMPEG_BEFORE_OPTIONS.split()
            if seek_seconds and seek_seconds > 0: ffmpeg_before_options_list = ['-ss', str(seek_seconds)] + ffmpeg_before_options_list
            final_ffmpeg_before_options = " ".join(ffmpeg_before_options_list)
            ffmpeg_main_options_list = [DEFAULT_FFMPEG_OPTIONS_AUDIO_ONLY]
            current_applied_filters = self.get_guild_ffmpeg_filters(guild_id)
            if current_applied_filters: ffmpeg_main_options_list.append(f'-af "{current_applied_filters}"')
            final_ffmpeg_main_options = " ".join(ffmpeg_main_options_list)
            ffmpeg_player_options_final = {'options': final_ffmpeg_main_options, 'before_options': final_ffmpeg_before_options}
            
            source = discord.FFmpegPCMAudio(stream_data_url, **ffmpeg_player_options_final)
            volume_source = discord.PCMVolumeTransformer(source, volume=self.get_guild_volume(guild_id))
            
            if vc.is_playing() or vc.is_paused() : vc.stop(); await asyncio.sleep(0.1) # Ensure stop completes
            if not vc.is_connected():
                print(f"DEBUG PLAY_QUEUE: VC disconnected for guild {guild_id} just before vc.play(). Aborting.") # Q12.1
                self._is_processing_next_song[guild_id] = False
                # Optionally put song back
                if song_info and not song_to_replay and self._queues.get(guild_id) is not None:
                     self._queues.setdefault(guild_id, []).insert(0, song_info)
                return

            after_callback = functools.partial(self._handle_after_play, guild_id)
            print(f"DEBUG PLAY_QUEUE: Calling vc.play() for '{self._current_song[guild_id].get('title')}' in guild {guild_id}") # Q13
            vc.play(volume_source, after=lambda e: self.loop.create_task(after_callback(e)))
            # self._is_processing_next_song[guild_id] = False # Reset flag *after* successfully starting play OR if play fails to start

            # Send Now Playing message (only if not seeking)
            if not seek_seconds:
                # ... (your existing Now Playing embed and message sending logic) ...
                # Ensure this uses self._current_song[guild_id] for details
                cs = self._current_song[guild_id] # Use the definitive current song
                embed = discord.Embed(title="🎶 Now Playing", description=f"[{cs['title']}]({cs['webpage_url']})", color=discord.Color.blurple())
                if cs.get('thumbnail'): embed.set_thumbnail(url=cs['thumbnail'])
                embed.add_field(name="Duration", value=format_duration(cs.get('duration', 0)))
                embed.add_field(name="Requested by", value=cs['requester'])
                embed.add_field(name="Volume", value=f"{int(self.get_guild_volume(guild_id) * 100)}%")
                embed.add_field(name="Loop", value=self.get_guild_loop_mode(guild_id).capitalize())
                embed.add_field(name="Effects", value=self.get_active_effects_display(guild_id), inline=False)
                
                if self._last_text_channel.get(guild_id):
                    target_channel_for_np = self._last_text_channel.get(guild_id)
                    if target_channel_for_np:
                        try:
                            np_view = NowPlayingView(guild_id=guild_id, song_requester_mention=cs['requester'])
                            np_msg = await target_channel_for_np.send(embed=embed, view=np_view)
                            self._interactive_np_message_ids[guild_id] = np_msg.id
                            np_view.message = np_msg 
                            print(f"DEBUG PLAY_QUEUE: Sent NP message with view for '{cs.get('title')}', ID: {np_msg.id}") # Q14
                        except Exception as e_np_send: 
                            print(f"ERROR PLAY_QUEUE: Failed to send NP message with view for guild {guild_id}: {e_np_send}")
                            try: await target_channel_for_np.send(embed=embed) # Fallback without view
                            except Exception as e_fallback: print(f"ERROR PLAY_QUEUE: Fallback NP send also failed: {e_fallback}")
            
            song_duration = self._current_song[guild_id].get('duration') # Use current song
            if isinstance(song_duration, (int, float)) and song_duration > UP_NEXT_NOTIFICATION_SECONDS and not self._current_song[guild_id].get('is_live_stream'):
                if guild_id in self._up_next_tasks: self._up_next_tasks[guild_id].cancel()
                self._up_next_tasks[guild_id] = self.loop.create_task(self.up_next_scheduler(guild_id, song_duration))
            
            # Successfully started playing or scheduled.
            self._is_processing_next_song[guild_id] = False # Reset flag HERE after play has started

        except discord.FFmpegNotFound:
            print(f"ERROR PLAY_QUEUE: FFmpeg not found for guild {guild_id}") # Q15
            if self._last_text_channel.get(guild_id): await self._last_text_channel[guild_id].send(embed=create_error_embed("FFmpeg not found. Please ensure FFmpeg is installed and in your system's PATH."))
            await self.disconnect_voice(guild_id) # Disconnect if FFmpeg is missing
            self._is_processing_next_song[guild_id] = False # Reset flag
        except Exception as e:
            print(f"ERROR PLAY_QUEUE: General error playing song in guild {guild_id} (title: {song_info.get('title')}): {type(e).__name__} - {e}") # Q16
            traceback.print_exc()
            if self._last_text_channel.get(guild_id): await self._last_text_channel[guild_id].send(embed=create_error_embed(f"Error playing '{song_info.get('title', 'Unknown')}': {e}"))
            self._is_processing_next_song[guild_id] = False # Reset flag before recursive call
            await self._play_guild_queue(guild_id) # Try to play next song in queue on error

    async def up_next_scheduler(self, guild_id: int, current_song_duration: float):
        # ... (ensure calls to self.save_guild_settings_to_file are correct if any) ...
        current_song_details = self._current_song.get(guild_id)
        if not current_song_details or current_song_details.get('is_live_stream'): return

        accumulated_time = current_song_details.get('accumulated_play_time_seconds', 0.0)
        current_segment_elapsed = 0.0
        if current_song_details.get('play_start_utc'): # This key is fine for runtime
             current_segment_elapsed = (datetime.datetime.now(timezone.utc) - current_song_details['play_start_utc']).total_seconds()
        total_elapsed_for_song = accumulated_time + current_segment_elapsed
        time_until_notification = max(0, current_song_duration - total_elapsed_for_song - UP_NEXT_NOTIFICATION_SECONDS)
        
        try: await asyncio.sleep(time_until_notification)
        except asyncio.CancelledError: return

        vc = self._voice_clients.get(guild_id)
        if not vc or not vc.is_playing() or not self._current_song.get(guild_id) or \
           self._current_song.get(guild_id, {}).get('webpage_url') != current_song_details.get('webpage_url') or \
           self._is_processing_next_song.get(guild_id):
            self._up_next_tasks.pop(guild_id, None); return

        next_song_info = self._queues.get(guild_id, [None])[0]
        if next_song_info and self._last_text_channel.get(guild_id):
            try:
                embed = discord.Embed(title="🔔 Up Next", description=f"[{next_song_info['title']}]({next_song_info['webpage_url']})", color=discord.Color.light_gray())
                embed.set_footer(text=f"Duration: {format_duration(next_song_info.get('duration'))} | Requested by: {next_song_info.get('requester', 'N/A')}")
                await self._last_text_channel[guild_id].send(embed=embed)
            except discord.HTTPException as e: print(f"Error sending Up Next notification: {e}")
        self._up_next_tasks.pop(guild_id, None)

    async def _handle_after_play(self, guild_id: int, error=None): # 'self' is the first parameter
        # NO 'client_instance = self' line needed here. Just use 'self'.
        print(f"\nDEBUG AFTER_PLAY: Called for guild {guild_id}. Error: {error}") # A1
        if self._is_processing_next_song.get(guild_id, False): # Use self.
            print(f"DEBUG AFTER_PLAY: Already processing next song for guild {guild_id}. Aborting.") # A1.1
            return
        
        if error:
            ignore_errors = ["operation not permitted", " जात", "error while decoding", "Premature end of stream", "ffmpeg process finished with exit code 1"]
            if not any(ign_err.lower() in str(error).lower() for ign_err in ignore_errors):
                print(f"Player error encountered in guild {guild_id}: {error}") # A2
                if self._last_text_channel.get(guild_id): # Use self.
                    try: await self._last_text_channel[guild_id].send(embed=create_error_embed(f"Playback error: {truncate_text(str(error), 100)}"))
                    except discord.HTTPException: pass
            else:
                print(f"DEBUG AFTER_PLAY: Ignored player error for guild {guild_id}: {error}") # A2.1
        
        song_that_just_finished = self._current_song.get(guild_id) # Use self.
        
        loop_mode = self.get_guild_loop_mode(guild_id) # Use self.
        is_24_7_on = self.get_guild_24_7_mode(guild_id)
        autoplay_genre = self.get_guild_autoplay_genre(guild_id)

        print(f"DEBUG AFTER_PLAY: Guild {guild_id} - Finished: '{song_that_just_finished.get('title') if song_that_just_finished else 'N/A'}'. Loop: {loop_mode}") # A3

        forced_skip = False
        if hasattr(self, f"_skip_forced_{guild_id}"): # Use self.
            forced_skip = getattr(self, f"_skip_forced_{guild_id}", False)
            if forced_skip:
                print(f"DEBUG AFTER_PLAY: Forced skip detected for guild {guild_id}.")
                delattr(self, f"_skip_forced_{guild_id}") 
        
        if song_that_just_finished and song_that_just_finished.get('is_live_stream') and \
           is_24_7_on and autoplay_genre and loop_mode == "off" and not forced_skip:
            print(f"DEBUG AFTER_PLAY: Live stream ended/errored in 24/7. Finding another for genre '{autoplay_genre}'.")
            if self._last_text_channel.get(guild_id): # Use self.
                try: await self._last_text_channel[guild_id].send(f"Live stream for '{autoplay_genre}' ended/errored. Finding another...")
                except discord.HTTPException: pass
            await self._play_guild_queue(guild_id) # Use self.
        elif loop_mode == "song" and song_that_just_finished and not forced_skip:
            print(f"DEBUG AFTER_PLAY: Loop 'song' active. Replaying '{song_that_just_finished.get('title')}'.")
            await self._play_guild_queue(guild_id, song_to_replay=song_that_just_finished.copy()) # Use self.
        else:
            if forced_skip and loop_mode == "song":
                print(f"DEBUG AFTER_PLAY: Loop 'song' was active but skip was forced. Playing next.")
            else:
                print(f"DEBUG AFTER_PLAY: Loop is '{loop_mode}' or skip forced. Playing next.")
            await self._play_guild_queue(guild_id) # Use self.

    async def schedule_leave(self, guild_id: int):
        # ... (ensure calls to self.save_guild_settings_to_file are correct if any) ...
        if self.get_guild_24_7_mode(guild_id): return
        if guild_id in self._leave_tasks and not self._leave_tasks[guild_id].done(): self._leave_tasks[guild_id].cancel()
        async def _leave_task_coro():
            await asyncio.sleep(AUTO_LEAVE_DELAY)
            vc = self._voice_clients.get(guild_id)
            if vc and vc.is_connected() and not self.get_guild_24_7_mode(guild_id):
                non_bot_members = [m for m in vc.channel.members if not m.bot]
                is_inactive = not vc.is_playing() and not self._queues.get(guild_id) and not self._current_song.get(guild_id)
                can_leave_due_to_inactivity = is_inactive and self.get_guild_loop_mode(guild_id) == "off"
                if not non_bot_members or can_leave_due_to_inactivity: 
                    msg_reason = "alone" if not non_bot_members else "due to inactivity"
                    if self._last_text_channel.get(guild_id):
                        try: await self._last_text_channel[guild_id].send(f"👋 Leaving {vc.channel.mention} as I'm {msg_reason}.")
                        except discord.HTTPException: pass
                    await self.disconnect_voice(guild_id)
            self._leave_tasks.pop(guild_id, None)
        self._leave_tasks[guild_id] = asyncio.create_task(_leave_task_coro())

    async def disconnect_voice(self, guild_id: int):
        await self.save_guild_settings_to_file(guild_id) # Corrected call
        if guild_id in self._voice_clients:
            vc = self._voice_clients.pop(guild_id)
            if vc.is_connected(): vc.stop(); await vc.disconnect(force=False)
        
        self._session_controllers.pop(guild_id, None)
        self._original_joiner.pop(guild_id, None)
        
        if guild_id in self._leave_tasks: self._leave_tasks[guild_id].cancel(); self._leave_tasks.pop(guild_id, None)
        if guild_id in self._up_next_tasks: self._up_next_tasks[guild_id].cancel(); self._up_next_tasks.pop(guild_id, None)
        self._is_processing_next_song.pop(guild_id, None)
        self._vote_skips.pop(guild_id, None)

        if self._interactive_np_message_ids.get(guild_id) and self._last_text_channel.get(guild_id):
            try:
                old_np_msg = await self._last_text_channel[guild_id].fetch_message(self._interactive_np_message_ids[guild_id])
                await old_np_msg.delete()
            except (discord.NotFound, discord.HTTPException): pass
            self._interactive_np_message_ids.pop(guild_id, None)

    async def cleanup_old_pending_searches(self):
        await self.wait_until_ready()
        while not self.is_closed():
            now = datetime.datetime.now(timezone.utc)
            users_to_pop = [uid for uid, data in self._pending_text_searches.items() if (now - data['timestamp']).total_seconds() > 120] # 'timestamp' is fine here, not saved
            for user_id in users_to_pop:
                pending_data = self._pending_text_searches.pop(user_id, None)
                if pending_data:
                    print(f"Cleaned up stale pending text search for user {user_id}")
                    try:
                        channel = self.get_channel(pending_data['channel_id'])
                        if channel and isinstance(channel, discord.TextChannel):
                            search_msg = await channel.fetch_message(pending_data['message_id'])
                            if search_msg and search_msg.embeds and search_msg.embeds[0].title and "Search Results" in search_msg.embeds[0].title:
                                await search_msg.edit(content="Search selection timed out.", embed=None, view=None)
                                await search_msg.clear_reactions()
                    except Exception: pass
            await asyncio.sleep(60)

    def get_active_effects_display(self, guild_id: int) -> str:
        # ... (rest of get_active_effects_display) ...
        filters_str = self.get_guild_ffmpeg_filters(guild_id)
        if not filters_str: return "Raw (No Filters)"
        if filters_str == DEFAULT_AUDIO_FILTERS: return "Default (Loudnorm)"

        active_effects = []
        if "bass=g=3" in filters_str: active_effects.append("Bass Boost (Low)")
        elif "bass=g=6" in filters_str: active_effects.append("Bass Boost (Medium)")
        elif "bass=g=9" in filters_str or "bass=g=12" in filters_str : active_effects.append("Bass Boost (High)")
        if "equalizer=f=1500:width_type=h:width=1000:g=3,equalizer=f=2500:width_type=h:width=1000:g=2" in filters_str : active_effects.append("Vocal Boost")
        if "treble=g=5" in filters_str : active_effects.append("Treble Boost")
        if "asetrate=48000*1.25" in filters_str and "atempo=1.20" in filters_str: active_effects.append("Nightcore")
        elif "asetrate=48000*0.8" in filters_str and "atempo=0.8" in filters_str and "aecho=0.8:0.9:500:0.3" in filters_str: active_effects.append("Vaporwave")
        if "stereotools=mlev=0.015" in filters_str : active_effects.append("Karaoke")
        if "asetrate=48000*1.05946" in filters_str and "atempo=0.94387" in filters_str: active_effects.append("Pitch Up")
        elif "asetrate=48000*0.94387" in filters_str and "atempo=1.05946" in filters_str: active_effects.append("Pitch Down")
        if "atempo=0.85" in filters_str and not any(x in active_effects for x in ["Vaporwave", "Pitch Down"]): active_effects.append("Slowed Tempo")
        if "atempo=1.15" in filters_str and not any(x in active_effects for x in ["Nightcore", "Pitch Up"]): active_effects.append("Sped Up Tempo")
        if "aecho=0.8:0.9:40:0.3" in filters_str and "Vaporwave" not in active_effects : active_effects.append("Reverb (Small)")
        elif "aecho=0.8:0.9:1000:0.3" in filters_str and "Vaporwave" not in active_effects : active_effects.append("Reverb (Large)")
        
        if not active_effects and filters_str != DEFAULT_AUDIO_FILTERS : return "Custom Filters Applied"
        return ", ".join(active_effects) if active_effects else "Default (Loudnorm)"

# --- Client Instantiation ---
intents = discord.Intents.all()
async def get_dynamic_prefix(bot_instance, message):
    if not message.guild:
        return commands.when_mentioned_or(bot_instance.default_prefix_val)(bot_instance, message)
    guild_prefixes = bot_instance.custom_prefixes.get(message.guild.id, [bot_instance.default_prefix_val])
    return commands.when_mentioned_or(*guild_prefixes)(bot_instance, message)
client = MyClient(intents=intents, command_prefix=get_dynamic_prefix)

# --- HELPER FUNCTIONS ---
def create_error_embed(message: str) -> discord.Embed:
    return discord.Embed(title="❌ Error", description=message, color=discord.Color.red())
def create_success_embed(title: str, message: str) -> discord.Embed:
    return discord.Embed(title=f"✅ {title}", description=message, color=discord.Color.green())
def create_info_embed(title: str, message: str) -> discord.Embed:
    return discord.Embed(title=f"ℹ️ {title}", description=message, color=discord.Color.blue())

def format_duration(seconds: Optional[Union[int, float]]) -> str:
    if seconds is None or not isinstance(seconds, (int, float)) or seconds < 0: return "N/A"
    seconds = int(seconds); hours = seconds // 3600; minutes = (seconds % 3600) // 60; secs = seconds % 60
    return f"{hours:02}:{minutes:02}:{secs:02}" if hours > 0 else f"{minutes:02}:{secs:02}"

def parse_timestamp(ts: str) -> Optional[float]:
    parts_str = ts.split(':');
    if not all(p.isdigit() for p in parts_str): return None
    parts = [int(p) for p in parts_str]
    if len(parts) == 3: return float(parts[0] * 3600 + parts[1] * 60 + parts[2])
    if len(parts) == 2: return float(parts[0] * 60 + parts[1])
    if len(parts) == 1: return float(parts[0])
    return None

def truncate_text(text: str, max_length: int) -> str:
    return text[:max_length - 3] + "..." if len(text) > max_length else text

# Global function or method of MyClient
async def get_audio_stream_info(url_or_query: str, search: bool = False, search_results_count: int = 1, search_provider: str = "youtube") -> Optional[Dict[str, Any]]:
    print(f"\nDEBUG YTDL (get_audio_stream_info): CALLED with url_or_query='{truncate_text(url_or_query, 100)}', search={search}, count={search_results_count}, provider_hint='{search_provider}'")

    ydl_opts = {
        'format': 'bestaudio/best', 'quiet': True, 'no_warnings': True, 
        'skip_download': True, 'source_address': '0.0.0.0',
        'youtube_skip_dash_manifest': True, 'allow_multiple_audio_streams': True,
    }

    actual_query_or_url = url_or_query
    if search:
        search_prefix = {"youtube": "ytsearch", "soundcloud": "scsearch", "youtubemusic": "ytmsearch", "ytmusic": "ytmsearch"}.get(search_provider.lower(), "ytsearch")
        
        # Ask for a few extra results to have a buffer for skipping Shorts
        # Only do this for YouTube searches.
        num_to_fetch = search_results_count
        if search_provider.lower() == "youtube":
            num_to_fetch += 5 

        actual_query_or_url = f"{search_prefix}{num_to_fetch}:{url_or_query}"
        
        ydl_opts.update({'noplaylist': False, 'dump_single_json': False, 
                         'extract_flat': 'discard_in_playlist' if search_results_count == 1 else True})
    else: 
        ydl_opts.update({'noplaylist': True, 'dump_single_json': True, 'extract_flat': False})

    print(f"DEBUG YTDL: ydl_opts: {ydl_opts}, ACTUAL query: '{actual_query_or_url}'")
    
    raw_info_from_ydl = None; error_message = None; processed_info = None

    try:
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            raw_info_from_ydl = await asyncio.to_thread(ydl.extract_info, actual_query_or_url, download=False)
            print(f"DEBUG YTDL: Raw info type: {type(raw_info_from_ydl)}. Content (500 chars): {str(raw_info_from_ydl)[:500]}")

            if not raw_info_from_ydl: error_message = "yt-dlp returned no information."
            
            # --- START OF MODIFIED SEARCH PROCESSING LOGIC ---
            elif search and isinstance(raw_info_from_ydl, dict) and raw_info_from_ydl.get('_type') == 'playlist' and 'entries' in raw_info_from_ydl:
                
                # Filter out YouTube Shorts from the entries list
                non_short_entries = []
                for entry in raw_info_from_ydl.get('entries', []):
                    # A simple and effective check for shorts
                    entry_url = entry.get('url', '')
                    if "youtube.com/shorts/" in entry_url:
                        print(f"DEBUG YTDL: Ignoring YouTube Short in search results: '{entry.get('title', 'N/A')}'")
                        continue # Skip this entry
                    
                    # Optional: Add duration check to filter out very long videos if desired
                    # duration = entry.get('duration')
                    # if isinstance(duration, (int, float)) and duration > (3600 * 2): # e.g., filter > 2 hours
                    #     print(f"DEBUG YTDL: Ignoring long video (>2h): '{entry.get('title')}'")
                    #     continue

                    non_short_entries.append(entry)

                # Now work with the filtered list
                if not non_short_entries:
                    error_message = "No valid songs found after filtering out YouTube Shorts."
                else:
                    if search_results_count > 1:
                        # Return a playlist-like dict with the filtered entries
                        processed_info = {
                            '_type': 'playlist',
                            'entries': non_short_entries[:search_results_count] # Trim to the originally requested count
                        }
                        print(f"DEBUG YTDL: Returning {len(processed_info['entries'])} non-Short results for multi-search.")
                    else: # search_results_count == 1
                        # Take the first non-Short entry
                        processed_info = non_short_entries[0]
                        print(f"DEBUG YTDL: Found first non-Short result: '{processed_info.get('title')}'")

            # --- END OF MODIFIED SEARCH PROCESSING LOGIC ---
            
            # Case for direct URL or if search logic above resulted in a single item dict
            elif isinstance(raw_info_from_ydl, dict) and raw_info_from_ydl.get('_type') != 'playlist':
                processed_info = raw_info_from_ydl

            # Check if after all that, we still have nothing
            if not processed_info and not error_message:
                error_message = "Could not process yt-dlp output into a usable format."
            
            # --- Post-processing for a single item (as before) ---
            if processed_info and isinstance(processed_info, dict) and not (processed_info.get('_type') == 'playlist' and 'entries' in processed_info):
                item_title_debug = processed_info.get('title', 'N/A')
                print(f"DEBUG YTDL: Processing single item: '{item_title_debug}'")
                
                # (The rest of the single item processing logic remains the same as the previous version)
                # It ensures webpage_url is set, re-fetches if formats are missing, and finds the stream url.
                # --- START OF COPIED SINGLE ITEM LOGIC ---
                if not processed_info.get('webpage_url'):
                    if processed_info.get('url') and "youtu" in processed_info.get('url'): processed_info['webpage_url'] = processed_info['url']
                    elif processed_info.get('extractor_key', '').lower() == 'youtube' and processed_info.get('id'): processed_info['webpage_url'] = f"https://www.youtube.com/watch?v={processed_info['id']}"
                    elif processed_info.get('extractor_key', '').lower() == 'soundcloud' and processed_info.get('permalink_url'): processed_info['webpage_url'] = processed_info.get('permalink_url')
                    elif processed_info.get('original_url'): processed_info['webpage_url'] = processed_info.get('original_url')
                    elif not search and url_or_query.startswith('http'): processed_info['webpage_url'] = url_or_query
                print(f"DEBUG YTDL: Populated/Checked webpage_url for '{item_title_debug}': {processed_info.get('webpage_url')}")
                if webpage_url := processed_info.get('webpage_url'):
                    if not processed_info.get('formats'):
                        print(f"DEBUG YTDL: Item '{item_title_debug}' missing formats, re-fetching from '{webpage_url}'.")
                        refetch_opts = ydl_opts.copy(); refetch_opts.update({'noplaylist': True, 'dump_single_json': True, 'extract_flat': False})
                        with yt_dlp.YoutubeDL(refetch_opts) as ydl_single:
                            try:
                                refetched_data = await asyncio.to_thread(ydl_single.extract_info, webpage_url, download=False)
                                if refetched_data and isinstance(refetched_data, dict):
                                    print(f"DEBUG YTDL: Re-fetch successful. Updating item.")
                                    processed_info.update(refetched_data)
                            except Exception as e_refetch: print(f"DEBUG YTDL: Re-fetch error: {e_refetch}")
                if processed_info.get('formats'):
                    best_audio_format = None; preferred_codecs = ['opus', 'vorbis', 'aac', 'mp4a', 'mp3']
                    for codec in preferred_codecs:
                        for f in reversed(processed_info.get('formats', [])):
                            if f.get('acodec') and codec in f['acodec'].lower() and f.get('url') and (f.get('vcodec') == 'none' or not f.get('vcodec')): best_audio_format = f; break
                        if best_audio_format: break
                    if not best_audio_format:
                        for f in reversed(processed_info.get('formats', [])):
                            if f.get('acodec') and f['acodec'] != 'none' and f.get('url') and (f.get('vcodec') == 'none' or not f.get('vcodec')): best_audio_format = f; break
                    if best_audio_format and best_audio_format.get('url'):
                        processed_info['url'] = best_audio_format['url']
                        print(f"DEBUG YTDL: Found playable stream URL in formats: ...{best_audio_format['url'][-50:]}")
                        for key in ['title', 'duration', 'uploader', 'thumbnail', 'abr', 'ext', 'is_live']:
                            if not processed_info.get(key) and best_audio_format.get(key) is not None: processed_info[key] = best_audio_format.get(key)
                    elif not processed_info.get('url') or "youtu" in processed_info.get('url'): error_message = "No suitable audio stream URL found in formats."
                elif not processed_info.get('url') or "youtu" in processed_info.get('url'): error_message = "No playable stream URL could be determined (no formats)."
                # --- END OF COPIED SINGLE ITEM LOGIC ---

    except yt_dlp_utils.DownloadError as e:
        error_message = f"DownloadError: {truncate_text(str(e), 100)}"
        title_fallback = (raw_info_from_ydl.get("title") if isinstance(raw_info_from_ydl, dict) else None) or url_or_query
        return {"error": error_message, "title": title_fallback}
    except Exception as e:
        error_message = f"Unexpected yt-dlp processing error: {truncate_text(str(e), 100)}"
        traceback.print_exc()
        title_fallback = (raw_info_from_ydl.get("title") if isinstance(raw_info_from_ydl, dict) else None) or url_or_query
        return {"error": error_message, "title": title_fallback}

    # ... (Final error handling and return logic - unchanged from previous version)
    if error_message:
        title_fallback = (processed_info.get("title") if isinstance(processed_info, dict) else None) or \
                         (raw_info_from_ydl.get("title") if isinstance(raw_info_from_ydl, dict) else None) or url_or_query
        print(f"DEBUG YTDL: Final error: {error_message}")
        return {"error": error_message, "title": title_fallback}
    if not processed_info:
        return {"error": "Failed to retrieve information (no specific error by yt-dlp).", "title": url_or_query}
    if isinstance(processed_info, dict) and not (processed_info.get('_type') == 'playlist' and 'entries' in processed_info):
        if not processed_info.get('webpage_url'):
            return {"error": "Could not determine a reference webpage URL for the item.", "title": processed_info.get('title', url_or_query)}
        if not processed_info.get('url'):
            return {"error": "Could not determine a playable stream URL for the item.", "title": processed_info.get('title', url_or_query)}
        if processed_info.get('webpage_url') == processed_info.get('url') and any(kw in processed_info.get('url') for kw in ['/watch?v=', 'youtu.be/', 'soundcloud.com/']):
            return {"error": "Identified webpage, but failed to extract a direct audio stream.", "title": processed_info.get('title', url_or_query)}
    
    has_stream_url = isinstance(processed_info, dict) and bool(processed_info.get('url')) and not any(kw in processed_info.get('url', '') for kw in ['/watch?v=', 'youtu.be/', 'soundcloud.com/'])
    print(f"DEBUG YTDL: Successfully processed. Title: '{processed_info.get('title', 'Playlist/Unknown') if isinstance(processed_info, dict) else 'Playlist'}'. Has potential stream: {has_stream_url}")
    return processed_info

async def fetch_lyrics(song_title: str, artist_name: Optional[str] = None) -> Optional[str]:
    search_artist = artist_name if artist_name else ""
    query_artist = re.sub(r'[^\w\s-]', '', search_artist).strip().replace(' ', '%20')
    query_title = re.sub(r'[^\w\s-]', '', song_title).strip().replace(' ', '%20')
    if not query_title: return None
    
    async with aiohttp.ClientSession() as session:
        if query_artist:
            url = f"https://api.lyrics.ovh/v1/{query_artist}/{query_title}"
            try:
                async with session.get(url, timeout=7) as response:
                    if response.status == 200: data = await response.json(); return data.get("lyrics", "").replace("\r\n", "\n")
            except asyncio.TimeoutError: print(f"Lyrics API timeout for {artist_name} - {song_title}")
            except Exception as e: print(f"Error fetching lyrics (with artist): {e}")

        final_query_artist_for_fallback = query_artist
        final_query_title_for_fallback = query_title

        if not artist_name:
            match = re.search(r"(.+?)\s*[-–—]\s*(.+)", song_title)
            if match:
                parsed_artist = re.sub(r'[^\w\s-]', '', match.group(1).strip()).replace(' ', '%20')
                parsed_title = re.sub(r'[^\w\s-]', '', match.group(2).strip()).replace(' ', '%20')
                if parsed_artist and parsed_title:
                    final_query_artist_for_fallback = parsed_artist
                    final_query_title_for_fallback = parsed_title
        
        fallback_url = f"https://api.lyrics.ovh/v1/{final_query_artist_for_fallback if final_query_artist_for_fallback else 'unknown'}/{final_query_title_for_fallback}"
        try:
            async with session.get(fallback_url, timeout=7) as response:
                if response.status == 200: data = await response.json(); return data.get("lyrics", "").replace("\r\n", "\n")
                else: return "Lyrics not found or API error."
        except asyncio.TimeoutError: return "Lyrics API timed out."
        except Exception as e: print(f"Error fetching lyrics (fallback): {e}"); return f"Could not fetch lyrics: Error. ({type(e).__name__})"
    return "Lyrics not found."

def load_user_playlists(user_id: int) -> Dict[str, List[Dict[str, Any]]]:
    playlist_path = client.get_user_playlist_path(user_id)
    if os.path.exists(playlist_path):
        try:
            with open(playlist_path, "r") as f: return json.load(f)
        except Exception as e: print(f"Error loading playlists for user {user_id}: {e}")
    return {}

def save_user_playlists(user_id: int, playlists_data: Dict[str, List[Dict[str, Any]]]):
    playlist_path = client.get_user_playlist_path(user_id)
    try:
        with open(playlist_path, "w") as f: json.dump(playlists_data, f, indent=4)
    except Exception as e: print(f"Error saving playlists for user {user_id}: {e}")

# --- Response Helper ---
async def send_custom_response(
    ctx_or_interaction: Union[commands.Context, discord.Interaction],
    content: Optional[str] = None,
    embed: Optional[discord.Embed] = None,
    ephemeral_preference: Optional[bool] = None,
    view: Optional[discord.ui.View] = None,
    target_channel_for_text: Optional[discord.TextChannel] = None
):
    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    final_ephemeral = False # Default to public

    # Determine send arguments
    send_kwargs = {}
    if content is not None:
        send_kwargs['content'] = content
    if embed is not None:
        send_kwargs['embed'] = embed
    if view is not None: # Only add view to kwargs if it's an actual View object
        send_kwargs['view'] = view
    
    if is_interaction:
        interaction: discord.Interaction = ctx_or_interaction
        if ephemeral_preference is None: final_ephemeral = True 
        elif isinstance(ephemeral_preference, bool): final_ephemeral = ephemeral_preference
        send_kwargs['ephemeral'] = final_ephemeral
        
        try:
            if interaction.response.is_done():
                await interaction.followup.send(**send_kwargs)
            else:
                await interaction.response.send_message(**send_kwargs)
        except discord.NotFound:
             if interaction.channel and isinstance(interaction.channel, discord.abc.Messageable):
                 # Remove ephemeral if sending to channel as fallback (ephemeral not supported)
                 if 'ephemeral' in send_kwargs: del send_kwargs['ephemeral']
                 await interaction.channel.send(**send_kwargs)
        except discord.HTTPException as e:
            print(f"Failed to send interaction response (ephemeral: {final_ephemeral}): {e}")
            if interaction.channel and isinstance(interaction.channel, discord.abc.Messageable) and not isinstance(e, discord.NotFound):
                 if 'ephemeral' in send_kwargs: del send_kwargs['ephemeral']
                 try: await interaction.channel.send(**send_kwargs)
                 except discord.HTTPException as e_fallback: print(f"Fallback send to channel also failed: {e_fallback}")

    else: # commands.Context
        context: commands.Context = ctx_or_interaction
        channel_to_send = target_channel_for_text if target_channel_for_text else context.channel
        if channel_to_send and isinstance(channel_to_send, discord.abc.Messageable):
            # Text commands don't take 'ephemeral' in send_kwargs for channel.send
            if 'ephemeral' in send_kwargs: del send_kwargs['ephemeral']
            
            try:
                message_obj = await channel_to_send.send(**send_kwargs)
                # If the view is the QueueView and this context initiated it, store the message
                # This is important for the QueueView's on_timeout to edit the correct message.
                if isinstance(view, QueueView) and context == view.interaction_or_ctx:
                    view.message_sent_by_bot = message_obj
            except discord.HTTPException as e: print(f"Failed to send text command response: {e}")
        else: print(f"Warning: Attempted to send response for text command but channel was None or not Messageable. Guild: {context.guild.id if context.guild else 'N/A'}")

# --- UI VIEWS ---
class SearchResultsView(discord.ui.View):
    def __init__(self, 
                 interaction: discord.Interaction, 
                 results: List[Dict[str, Any]], 
                 original_query: str, # The user's raw query, e.g., "lofi hip hop"
                 current_platform: str, # "youtube" or "soundcloud"
                 parent_message_id: Optional[int] = None # To edit the original search message
                ):
        super().__init__(timeout=45.0) # Slightly longer timeout for platform switch
        self.interaction = interaction # Original interaction that triggered this view
        self.results = results
        self.original_query = original_query 
        self.current_platform = current_platform.lower()
        self.selected_song_info: Optional[Dict[str, Any]] = None
        self.switched_platform: bool = False
        self.parent_message_id = parent_message_id # The ID of the message showing "Search Results for..."

        # Add buttons for song selection
        for i, result in enumerate(results):
            title = result.get('title') or result.get('fulltitle', 'Unknown Title')
            duration_str = format_duration(result.get('duration'))
            label = truncate_text(f"{i+1}. {title} ({duration_str})", 80)
            # Ensure custom_id is unique and identifiable
            self.add_item(SearchResultButton(label=label, custom_id=f"search_select_{i}_{interaction.id}", song_info=result, row= i // MAX_SEARCH_RESULTS_PER_ROW))

        # Add platform switch button
        other_platform = "SoundCloud" if self.current_platform == "youtube" else "YouTube"
        switch_button = discord.ui.Button(
            label=f"↺ Search on {other_platform}",
            style=discord.ButtonStyle.primary, # or .secondary
            custom_id=f"search_switch_platform_{interaction.id}", # Unique ID
            row= (len(results) // MAX_SEARCH_RESULTS_PER_ROW) + 1 # Place it on a new row
        )
        switch_button.callback = self.switch_platform_callback # Assign callback directly
        self.add_item(switch_button)

    async def switch_platform_callback(self, interaction: discord.Interaction):
        """Callback for the platform switch button."""
        if interaction.user.id != self.interaction.user.id: # Only original user
            await interaction.response.send_message("You did not initiate this search.", ephemeral=True)
            return

        await interaction.response.defer() # Acknowledge the button click
        self.switched_platform = True
        self.stop() # Stop this current view

        new_platform = "soundcloud" if self.current_platform == "youtube" else "youtube"
        
        # Let the original command handler know to re-search
        # We can signal this by editing the original interaction's message or by how _handle_play_logic is called.
        # For simplicity, we'll assume the original _handle_play_logic is re-invoked
        # by whatever called it initially, but this time with the new platform hint.

        # The interaction that spawned this view (self.interaction) needs to be
        # effectively "re-run" but with a modified query for the new platform.
        # This is a bit tricky as we can't directly re-invoke a slash command's callback easily from here.

        # ---- Approach: Edit original message and let user re-issue command or have _handle_play_logic handle it ----
        # This is simpler than trying to re-trigger the command flow perfectly.
        # We'll edit the original search results message to indicate the switch.
        
        try:
            # Try to edit the original message that spawned this view
            original_interaction_response = await self.interaction.original_response()
            await original_interaction_response.edit(
                content=f"Switching search for '{self.original_query}' to {new_platform.capitalize()}...",
                embed=None,
                view=None
            )
        except (discord.NotFound, discord.HTTPException) as e:
            print(f"Error editing original search message on platform switch: {e}")
            # If edit fails, send a new message
            await interaction.followup.send(f"Switching search for '{self.original_query}' to {new_platform.capitalize()}...",ephemeral=True)


        # Now, we need to trigger a new search. The easiest way is to have the calling function
        # (likely _handle_play_logic) check a flag or value returned by this view.
        # Since the view stops, _handle_play_logic's `await search_view_instance.wait()` will return.
        # It can then check `search_view_instance.switched_platform` and `search_view_instance.current_platform` (which is the *old* one).

    async def on_timeout(self):
        if self.switched_platform or self.selected_song_info: # If an action was taken, don't say "timed out"
            self.stop()
            return

        for item in self.children:
            if isinstance(item, discord.ui.Button): item.disabled = True
        
        try:
            # Try to edit the original message that spawned this view
            original_interaction_response = await self.interaction.original_response()
            await original_interaction_response.edit(
                content=f"Search selection for '{self.original_query}' on {self.current_platform.capitalize()} timed out.",
                view=self, # Keep the disabled buttons
                embed=None
            )
        except (discord.NotFound, discord.HTTPException) as e:
            print(f"Error editing search view on timeout: {e}")
        self.stop()

# SearchResultButton remains mostly the same, but ensure custom_id is unique
class SearchResultButton(discord.ui.Button):
    def __init__(self, label: str, custom_id: str, song_info: Dict[str, Any], row: int):
        super().__init__(label=label, custom_id=custom_id, style=discord.ButtonStyle.secondary, row=row)
        self.song_info = song_info

    async def callback(self, interaction: discord.Interaction):
        # Defer the response, as we'll edit the original message
        await interaction.response.defer()
        view: SearchResultsView = self.view # type: ignore

        # Basic check if the interactor is the one who initiated the search
        if interaction.user.id != view.interaction.user.id:
            await interaction.followup.send("You did not initiate this search.", ephemeral=True)
            return

        view.selected_song_info = self.song_info
        for item_child in view.children: # Corrected variable name
            if isinstance(item_child, discord.ui.Button): item_child.disabled = True
        
        title_display = self.song_info.get('title', 'Unknown Title')
        try:
            # Edit the original message that this view is attached to
            original_interaction_response = await view.interaction.original_response()
            await original_interaction_response.edit(
                content=f"Selected: **{truncate_text(str(title_display), 100)}** from {view.current_platform.capitalize()}.\nAdding to queue...", 
                view=view, # Keep the view with disabled buttons
                embed=None
            )
        except (discord.NotFound, discord.HTTPException) as e:
            print(f"Error editing original response after search selection: {e}")
            # Fallback if original edit fails
            await interaction.followup.send(f"Selected: **{truncate_text(str(title_display), 100)}**. Adding to queue...", ephemeral=True)
        
        view.stop()

class QueueView(discord.ui.View):
    def __init__(self, interaction_or_ctx: Union[discord.Interaction, commands.Context], guild_id: int, current_page: int = 0, songs_per_page: int = 10):
        super().__init__(timeout=180.0)
        self.interaction_or_ctx = interaction_or_ctx
        self.guild_id = guild_id
        self.current_page = current_page
        self.songs_per_page = songs_per_page
        self.user_id = interaction_or_ctx.user.id if isinstance(interaction_or_ctx, discord.Interaction) else interaction_or_ctx.author.id
        self.message_sent_by_bot: Optional[discord.Message] = None # For text command timeout
        # Buttons are now defined below with decorators
        self._update_button_states() # Initial state update

    def get_current_page_songs(self) -> List[Dict[str, Any]]:
        # ... (same as before)
        queue = client._queues.get(self.guild_id, []); start_index = self.current_page * self.songs_per_page
        return queue[start_index : start_index + self.songs_per_page]

    def get_queue_embed(self) -> discord.Embed:
        # ... (same as before)
        queue = client._queues.get(self.guild_id, []); current = client._current_song.get(self.guild_id)
        page_songs = self.get_current_page_songs()
        embed = discord.Embed(title=f"🎶 Song Queue (Page {self.current_page + 1})", color=discord.Color.purple())
        if current: embed.add_field(name="▶️ Now Playing", value=f"[{truncate_text(current['title'],60)}]({current['webpage_url']}) - {format_duration(current['duration'])} (Req: {current['requester']})", inline=False)
        if page_songs:
            description_lines = [f"{self.current_page * self.songs_per_page + 1 + i}. [{truncate_text(song['title'], 50)}]({song['webpage_url']}) - {format_duration(song['duration'])} (Req: {song['requester']})" for i, song in enumerate(page_songs)]
            embed.description = "\n".join(description_lines)
        elif not current : embed.description = "The queue is empty!"
        total_songs = len(queue); total_pages = max(1, (total_songs + self.songs_per_page -1) // self.songs_per_page)
        embed.set_footer(text=f"Page {self.current_page + 1}/{total_pages}. Total songs: {total_songs}")
        return embed

    def _update_button_states(self):
        """Updates the disabled state of the buttons."""
        queue = client._queues.get(self.guild_id, [])
        total_pages = max(1, (len(queue) + self.songs_per_page - 1) // self.songs_per_page)

        # Access buttons by their custom_id or by iterating children
        prev_button = discord.utils.get(self.children, custom_id="q_prev_btn")
        next_button = discord.utils.get(self.children, custom_id="q_next_btn")
        shuffle_button = discord.utils.get(self.children, custom_id="q_shuf_btn")
        clear_button = discord.utils.get(self.children, custom_id="q_clr_btn")

        if prev_button: prev_button.disabled = (self.current_page == 0)
        if next_button: next_button.disabled = (self.current_page >= total_pages - 1)
        
        # Controller buttons are always present but their callback checks permissions
        is_ctrl = client.is_controller(self.interaction_or_ctx)
        if shuffle_button: shuffle_button.disabled = not is_ctrl or len(queue) <= 1
        if clear_button: clear_button.disabled = not is_ctrl or not queue


    @discord.ui.button(label="⬅️ Prev", style=discord.ButtonStyle.grey, custom_id="q_prev_btn", row=0)
    async def prev_page_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This view is not for you.", ephemeral=True); return
        if self.current_page > 0:
            self.current_page -= 1
        self._update_button_states()
        await interaction.response.edit_message(embed=self.get_queue_embed(), view=self)

    @discord.ui.button(label="Next ➡️", style=discord.ButtonStyle.grey, custom_id="q_next_btn", row=0)
    async def next_page_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This view is not for you.", ephemeral=True); return
        queue = client._queues.get(self.guild_id, [])
        total_pages = max(1, (len(queue) + self.songs_per_page - 1) // self.songs_per_page)
        if self.current_page < total_pages - 1:
            self.current_page += 1
        self._update_button_states()
        await interaction.response.edit_message(embed=self.get_queue_embed(), view=self)

    @discord.ui.button(label="🔀 Shuffle", style=discord.ButtonStyle.blurple, custom_id="q_shuf_btn", row=1)
    async def shuffle_queue_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not client.is_controller(interaction): # Check current interactor
            await interaction.response.send_message(embed=create_error_embed("Only controllers can shuffle."), ephemeral=True); return
        
        queue = client._queues.get(self.guild_id, [])
        if len(queue) > 1:
            random.shuffle(queue)
            await client.save_guild_settings_to_file(self.guild_id)
            self.current_page = 0 # Reset to first page after shuffle
            self._update_button_states()
            await interaction.response.edit_message(embed=self.get_queue_embed(), view=self)
            # Followup for shuffle confirmation (original response was edit_message)
            await interaction.followup.send("🔀 Queue shuffled!", ephemeral=True)
        else:
            await interaction.response.send_message(embed=create_error_embed("Not enough songs in queue to shuffle."), ephemeral=True)

    @discord.ui.button(label="🗑️ Clear", style=discord.ButtonStyle.red, custom_id="q_clr_btn", row=1)
    async def clear_queue_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if not client.is_controller(interaction): # Check current interactor
            await interaction.response.send_message(embed=create_error_embed("Only controllers can clear the queue."), ephemeral=True); return

        client._queues[self.guild_id] = []
        await client.save_guild_settings_to_file(self.guild_id)
        self.current_page = 0 # Reset to first page
        self._update_button_states()
        await interaction.response.edit_message(embed=self.get_queue_embed(), view=self)
        await interaction.followup.send("🗑️ Queue cleared!", ephemeral=True)


    async def on_timeout(self):
        # ... (same as before, but access buttons via self.children or specific custom_ids to disable)
        for item in self.children:
            if isinstance(item, discord.ui.Button):
                item.disabled = True
        try:
            if isinstance(self.interaction_or_ctx, discord.Interaction):
                # If the view was attached to an existing message (not common for initial send)
                # or if it was part of the original response.
                if self.interaction_or_ctx.message:
                     await self.interaction_or_ctx.message.edit(view=self) # type: ignore
                else: # Original response
                     await self.interaction_or_ctx.edit_original_response(view=self)
            elif isinstance(self.interaction_or_ctx, commands.Context):
                if self.message_sent_by_bot:
                    await self.message_sent_by_bot.edit(view=self)
        except discord.NotFound: pass # Message might have been deleted
        except discord.HTTPException as e: print(f"Error disabling queue view on timeout: {e}")
        self.stop()

async def _display_queue_view_logic(interaction_or_ctx: Union[discord.Interaction, commands.Context]):
    # This function will contain the core logic from your original music_queue_view_slash
    # and the text_queue command.
    
    # Determine guild_id and user_id based on type
    if isinstance(interaction_or_ctx, discord.Interaction):
        guild_id = interaction_or_ctx.guild_id
        user_id = interaction_or_ctx.user.id
        if not guild_id: # Should not happen for guild commands
            await send_custom_response(interaction_or_ctx, embed=create_error_embed("Command unavailable in DMs."), ephemeral_preference=True)
            return
    elif isinstance(interaction_or_ctx, commands.Context):
        if not interaction_or_ctx.guild:
            await send_custom_response(interaction_or_ctx, embed=create_error_embed("Command unavailable in DMs."), ephemeral_preference=False)
            return
        guild_id = interaction_or_ctx.guild.id
        user_id = interaction_or_ctx.author.id
    else:
        # Should not happen with typical usage
        print("ERROR: _display_queue_view_logic called with unknown type.")
        return

    if not client._queues.get(guild_id) and not client._current_song.get(guild_id):
        # Determine ephemeral preference based on type
        ephemeral_pref = isinstance(interaction_or_ctx, discord.Interaction)
        await send_custom_response(
            interaction_or_ctx,
            embed=discord.Embed(title="🎶 Queue", description="The queue is empty!", color=discord.Color.blue()),
            ephemeral_preference=ephemeral_pref
        )
        return

    # For text commands, page might be passed differently.
    # For this unified logic, we'll assume page 0 for button clicks.
    # If called from text command, `page` arg handling would be in the text command itself.
    current_page_from_btn = 0 # Button always starts at page 0 (page 1 for user)
    
    view = QueueView(interaction_or_ctx, guild_id, current_page=current_page_from_btn)
    
    # send_custom_response handles ephemeral and response/followup for interactions
    # For text commands, it just sends to channel.
    await send_custom_response(
        interaction_or_ctx,
        embed=view.get_queue_embed(),
        view=view,
        ephemeral_preference=False # Queue view is usually public
    )

class NowPlayingView(discord.ui.View):
    def __init__(self, guild_id: int, song_requester_mention: str):
        super().__init__(timeout=None) # Persistent while song plays
        self.guild_id = guild_id
        # Storing requester_mention to compare with interaction.user for some permissions
        self.song_requester_mention = song_requester_mention
        self.message: Optional[discord.Message] = None 

        # Dynamically update button states based on current conditions (e.g., loop mode for loop button label)
        # This could be done here or via a separate update method called before sending.
        # For simplicity, we'll keep labels static here and user learns current state from embed or commands.

    # --- Permission Helper Methods ---
    async def _get_member_from_interaction(self, interaction: discord.Interaction) -> Optional[discord.Member]:
        if not interaction.guild: return None
        member = interaction.guild.get_member(interaction.user.id)
        # Fallback if interaction.user is somehow not a Member object already
        if not member and isinstance(interaction.user, discord.User): 
            try: member = await interaction.guild.fetch_member(interaction.user.id)
            except (discord.NotFound, discord.HTTPException): return None
        return member

    async def _check_controller(self, interaction: discord.Interaction) -> bool:
        # ... (Your existing _check_controller method - ensure it uses client instance correctly) ...
        # Example: client.is_controller(...)
        member_obj = await self._get_member_from_interaction(interaction)
        if not member_obj:
            if not interaction.response.is_done(): await interaction.response.send_message("Could not verify permissions (member).", ephemeral=True)
            else: await interaction.followup.send("Could not verify permissions (member).", ephemeral=True)
            return False
        
        class TempContext: # Minimal context for client.is_controller
            def __init__(self, guild_obj, member_obj_ctx, channel_obj):
                self.guild = guild_obj; self.user = member_obj_ctx; self.author = member_obj_ctx; self.channel = channel_obj
        
        if not client.is_controller(TempContext(interaction.guild, member_obj, interaction.channel)):
            if not interaction.response.is_done(): await interaction.response.send_message("Only controllers can use this button.", ephemeral=True)
            else: await interaction.followup.send("Only controllers can use this button.", ephemeral=True)
            return False
        return True


    async def _check_controller_or_requester(self, interaction: discord.Interaction) -> bool:
        # ... (Your existing _check_controller_or_requester method - ensure it uses client instance and robust requester ID check) ...
        member_obj = await self._get_member_from_interaction(interaction)
        if not member_obj:
            if not interaction.response.is_done(): await interaction.response.send_message("Could not verify permissions (member).", ephemeral=True)
            else: await interaction.followup.send("Could not verify permissions (member).", ephemeral=True)
            return False

        class TempContext:
             def __init__(self, guild_obj, member_obj_ctx, channel_obj):
                self.guild = guild_obj; self.user = member_obj_ctx; self.author = member_obj_ctx; self.channel = channel_obj
        
        is_ctrl = client.is_controller(TempContext(interaction.guild, member_obj, interaction.channel))
        
        is_req = False
        current_song_data = client._current_song.get(self.guild_id)
        if current_song_data and current_song_data.get('requester'):
            match_id = re.match(r"<@!?(\d+)>", current_song_data['requester'])
            if match_id: is_req = (interaction.user.id == int(match_id.group(1)))
            elif current_song_data['requester'] == interaction.user.mention: is_req = True # Fallback

        if not (is_ctrl or is_req):
            if not interaction.response.is_done(): await interaction.response.send_message("Only controllers or the song requester can use this button.", ephemeral=True)
            else: await interaction.followup.send("Only controllers or the song requester can use this button.", ephemeral=True)
            return False
        return True

    # --- Row 0: Core Controls ---
    @discord.ui.button(emoji="⏪", label="Replay", style=discord.ButtonStyle.secondary, row=0, custom_id="np_view_replay_btn")
    async def replay_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return

        current_song = client._current_song.get(self.guild_id)
        vc = client._voice_clients.get(self.guild_id)

        if not vc or not current_song or current_song.get('is_live_stream'):
            await send_custom_response(interaction, embed=create_error_embed("Cannot replay: No song or it's live."), ephemeral_preference=True)
            return
        
        await interaction.response.defer(ephemeral=False) # Action is public
        print(f"DEBUG NP_VIEW: Replay clicked for '{current_song.get('title')}'")
        await client._play_guild_queue(self.guild_id, song_to_replay=current_song.copy(), seek_seconds=0.0)
        # _play_guild_queue sends new NP. Optional followup:
        await interaction.followup.send(f"🔄 Replaying **{truncate_text(current_song.get('title', 'song'), 40)}**.", ephemeral=True)


    @discord.ui.button(emoji="⏯️", label="Pause/Resume", style=discord.ButtonStyle.primary, row=0, custom_id="np_view_pause_resume_btn") 
    async def pause_resume_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return
        
        vc = client._voice_clients.get(self.guild_id)
        # Defer first, then call logic handlers which will send followups
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=False) # Action is public

        if vc and vc.is_playing():
            await _handle_pause_logic(interaction) 
        elif vc and vc.is_paused():
            await _handle_resume_logic(interaction)
        else:
            await interaction.followup.send("Not currently playing or paused to toggle.", ephemeral=True)


    @discord.ui.button(emoji="⏭️", label="Skip", style=discord.ButtonStyle.secondary, row=0, custom_id="np_view_skip_btn")
    async def skip_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller_or_requester(interaction): return
        # _handle_skip_logic will defer and respond.
        await _handle_skip_logic(interaction)

    @discord.ui.button(emoji="⏹️", label="Stop", style=discord.ButtonStyle.danger, row=0, custom_id="np_view_stop_btn")
    async def stop_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return
        await _handle_stop_logic(interaction) # Handles its own response/deferral
        if self.message: 
            try: await self.message.delete() # Delete the NP message as playback stopped
            except: pass 
        self.stop() # Stop this view

    # --- Row 1: More Controls ---
    @discord.ui.button(emoji="🔉", label="-", style=discord.ButtonStyle.secondary, row=1, custom_id="np_view_vol_down_btn")
    async def volume_down_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return

        current_volume_guild = client.get_guild_volume(self.guild_id) # This is 0.0 to 2.0
        new_volume_player = max(0.0, current_volume_guild - 0.10) 
        new_volume_setting_int = round(new_volume_player * 100) # For _handle_settings_volume_logic (0-200)

        # _handle_settings_volume_logic handles deferral and response.
        # It also saves the volume as the new default.
        await _handle_settings_volume_logic(interaction, new_volume_setting_int)
        # Optional: Update the embed if you want the NP message to refresh instantly (more complex)
        # For now, _handle_settings_volume_logic sends its own confirmation.

    @discord.ui.button(emoji="🔊", label="+", style=discord.ButtonStyle.secondary, row=1, custom_id="np_view_vol_up_btn")
    async def volume_up_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return
        
        current_volume_guild = client.get_guild_volume(self.guild_id)
        new_volume_player = min(2.0, current_volume_guild + 0.10) 
        new_volume_setting_int = round(new_volume_player * 100)
        
        await _handle_settings_volume_logic(interaction, new_volume_setting_int)

    @discord.ui.button(emoji="🔁", label="Loop", style=discord.ButtonStyle.secondary, row=1, custom_id="np_view_loop_btn")
    async def loop_toggle_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id or not await self._check_controller(interaction): return
        
        current_loop = client.get_guild_loop_mode(self.guild_id)
        next_loop_mode = "off" 
        if current_loop == "off": next_loop_mode = "song"
        elif current_loop == "song": next_loop_mode = "queue"
        
        await _handle_settings_loop_logic(interaction, next_loop_mode) # Handles its own response/deferral

    @discord.ui.button(emoji="📜", label="Queue", style=discord.ButtonStyle.primary, row=1, custom_id="np_view_queue_btn")
    async def view_queue_button(self, interaction: discord.Interaction, button: discord.ui.Button):
        if interaction.guild_id != self.guild_id: return # User from another guild clicked somehow

        # Anyone can view the queue. _display_queue_view_logic handles its own responses.
        # Defer here to acknowledge button click immediately.
        if not interaction.response.is_done():
            await interaction.response.defer(ephemeral=False, thinking=False) # Queue view is public.
        
        await _display_queue_view_logic(interaction) # Make sure this function is accessible

# --- SLASH COMMAND GROUPS ---
music_group = app_commands.Group(name="music", description="Music related commands.")
music_controls_group = app_commands.Group(name="controls", description="Playback controls.", parent=music_group)
music_queue_group = app_commands.Group(name="queue", description="Manage the song queue.", parent=music_group)
music_settings_group = app_commands.Group(name="settings", description="Configure music bot settings.", parent=music_group)
effects_group = app_commands.Group(name="effects", description="Apply audio effects.", parent=music_group)
controller_group = app_commands.Group(name="controller", description="Manage session controllers.", parent=music_group)
playlist_group = app_commands.Group(name="playlist", description="Manage personal playlists.", parent=music_group)

# --- MUSIC SLASH COMMANDS ---
@music_group.command(name="play", description="Plays a song/video URL or searches YouTube/SoundCloud.")
@app_commands.describe(query="URL, search query, 'sc:<query>' for SoundCloud, or 'yt:<query>' for YouTube.")
@app_commands.checks.cooldown(1, 3.0, key=lambda i: (i.guild_id, i.user.id))
async def music_play_slash(interaction: discord.Interaction, query: str):
    """
    Slash command to play music.
    Parses query for prefixes like 'sc:' (SoundCloud) or 'yt:' (YouTube explicit search).
    Defaults to YouTube search for unprefixed terms. Handles direct URLs.
    """
    # Preliminary check: User must be in a voice channel
    if not interaction.user.voice or not interaction.user.voice.channel:
        await send_custom_response(
            interaction,
            embed=create_error_embed("You need to be in a voice channel to use this command."),
            ephemeral_preference=True
        )
        return

    # Call the shared logic handler (assuming it's a method of your client instance)
    await client._handle_play_logic(interaction, query)

@music_controls_group.command(name="join", description="Makes the bot join your current voice channel.")
async def music_join_slash(interaction: discord.Interaction):
    vc = await client.ensure_voice_client(interaction, join_if_not_connected=True)
    if vc :
        # ensure_voice_client handles its own errors now via send_custom_response
        # Only send success if interaction wasn't responded to by ensure_voice_client error
        if not interaction.response.is_done(): # Check if ensure_voice_client already responded
            await send_custom_response(interaction, embed=create_success_embed("Joined VC", f"Connected to {vc.channel.mention}."), ephemeral_preference=False)
    # No explicit else for error, as ensure_voice_client should handle it.

@music_controls_group.command(name="skip", description="Skips the current song.")
@app_commands.checks.cooldown(1, 2.0, key=lambda i: (i.guild_id, i.user.id))
async def music_skip_slash(interaction: discord.Interaction): await _handle_skip_logic(interaction)

@music_controls_group.command(name="voteskip", description="Starts a vote to skip the current song.")
@app_commands.checks.cooldown(1, 30.0, key=lambda i: i.guild_id)
async def music_voteskip_slash(interaction: discord.Interaction):
    guild_id = interaction.guild_id; vc = client._voice_clients.get(guild_id); current_song_info = client._current_song.get(guild_id)
    if not vc or not vc.is_connected() or not current_song_info:
        await send_custom_response(interaction, embed=create_error_embed("Not playing anything."), ephemeral_preference=True); return
    if not interaction.user.voice or interaction.user.voice.channel != vc.channel:
        await send_custom_response(interaction, embed=create_error_embed("You must be in the same voice channel to start a voteskip."), ephemeral_preference=True); return
    
    active_poll_msg_id = next((msg_id for msg_id in client._vote_skips.get(guild_id, {})), None)
    if active_poll_msg_id:
        await send_custom_response(interaction, embed=create_error_embed("A voteskip poll is already active in this server."), ephemeral_preference=True)
        return

    await interaction.response.defer(ephemeral=True, thinking=True)
    
    listeners_in_vc = [m for m in vc.channel.members if not m.bot and m.voice and m.voice.channel == vc.channel]
    required_votes = max(1, int(len(listeners_in_vc) * VOTE_SKIP_PERCENTAGE)) if listeners_in_vc else 1
    
    embed = discord.Embed(title="🗳️ Vote to Skip Song", description=f"**{interaction.user.display_name}** wants to skip **{truncate_text(current_song_info['title'], 60)}**.", color=discord.Color.gold())
    embed.add_field(name="Votes", value=f"1 / {required_votes}", inline=False)
    embed.set_footer(text="Poll active for 60 seconds.")
    
    public_vote_message = await interaction.channel.send(embed=embed)
    client._vote_skips.setdefault(guild_id, {})[public_vote_message.id] = [interaction.user.id]
    
    vote_view = View(timeout=60.0)
    yes_button = Button(label="✅ Vote Yes", style=discord.ButtonStyle.green, custom_id=f"internal_voteskip_yes_{public_vote_message.id}")
    vote_view.add_item(yes_button)
    
    await public_vote_message.edit(view=vote_view)
    await interaction.followup.send("Voteskip poll started!", ephemeral=True)

    async def cleanup_poll():
        await asyncio.sleep(60.5)
        if public_vote_message.id in client._vote_skips.get(guild_id, {}):
            client._vote_skips[guild_id].pop(public_vote_message.id, None)
            try:
                ended_embed = embed.copy(); ended_embed.description += "\n\n**This poll has ended (timeout).**"; ended_embed.color = discord.Color.light_grey()
                for item_btn in vote_view.children:
                    if isinstance(item_btn, Button): item_btn.disabled = True # Check if it's a button
                await public_vote_message.edit(embed=ended_embed, view=vote_view)
            except (discord.NotFound, discord.HTTPException): pass
    client.loop.create_task(cleanup_poll())


@music_controls_group.command(name="stop", description="Stops playback, clears queue, and leaves.")
async def music_stop_slash(interaction: discord.Interaction): await _handle_stop_logic(interaction)

@music_controls_group.command(name="nowplaying", description="Shows the currently playing song.")
async def music_nowplaying_slash(interaction: discord.Interaction): await _handle_nowplaying_logic(interaction)

@music_controls_group.command(name="leave", description="Makes the bot leave the voice channel.")
async def music_leave_slash(interaction: discord.Interaction): await _handle_leave_logic(interaction)

@music_controls_group.command(name="pause", description="Pauses the current playback.")
async def music_pause_slash(interaction: discord.Interaction): await _handle_pause_logic(interaction)

@music_controls_group.command(name="resume", description="Resumes paused playback.")
async def music_resume_slash(interaction: discord.Interaction): await _handle_resume_logic(interaction)

@music_controls_group.command(name="seek", description="Seeks to a timestamp in the current song.")
@app_commands.describe(timestamp="Timestamp (HH:MM:SS, MM:SS, or SS).")
async def music_seek_slash(interaction: discord.Interaction, timestamp: str): await _handle_seek_logic(interaction, timestamp)

@music_group.command(name="lyrics", description="Shows lyrics for the current or a specified song.")
@app_commands.describe(song_title="Optional: Specific song title to search lyrics for.")
async def music_lyrics_slash(interaction: discord.Interaction, song_title: Optional[str] = None): await _handle_lyrics_logic(interaction, song_title)

@music_queue_group.command(name="view", description="Shows the current song queue.")
async def music_queue_view_slash(interaction: discord.Interaction):
    # Deferral is handled by send_custom_response if needed, or do it here if _display_queue_view_logic is long
    # if not interaction.response.is_done():
    # await interaction.response.defer(ephemeral=False) # Defer if logic is long
    await _display_queue_view_logic(interaction)

@music_queue_group.command(name="clear", description="Clears all songs from the queue.")
async def music_queue_clear_slash(interaction: discord.Interaction): await _handle_queue_clear_logic(interaction)

@music_queue_group.command(name="remove", description="Removes song by index or title part.")
@app_commands.describe(identifier="Index (1-based) or part of title.")
async def music_queue_remove_slash(interaction: discord.Interaction, identifier: str): await _handle_queue_remove_logic(interaction, identifier)

@music_queue_group.command(name="removerange", description="Removes a range of songs from queue by index.")
@app_commands.describe(start_index="1-based start index.", end_index="1-based end index.")
async def music_queue_removerange_slash(interaction: discord.Interaction, start_index: int, end_index: int): await _handle_queue_removerange_logic(interaction, start_index, end_index)

@music_queue_group.command(name="shuffle", description="Shuffles the current song queue.")
async def music_queue_shuffle_slash(interaction: discord.Interaction): await _handle_queue_shuffle_logic(interaction)

@music_queue_group.command(name="move", description="Moves a song in queue to new position.")
@app_commands.describe(from_index="Current 1-based index.", to_index="New 1-based index.")
async def music_queue_move_slash(interaction: discord.Interaction, from_index: int, to_index: int): await _handle_queue_move_logic(interaction, from_index, to_index)

@music_queue_group.command(name="jump", description="Jumps to a song in queue, playing it next.")
@app_commands.describe(identifier="1-based Index or part of title.")
async def music_queue_jump_slash(interaction: discord.Interaction, identifier: str): await _handle_queue_jump_logic(interaction, identifier)

@music_queue_group.command(name="export", description="Exports current queue to a text file of URLs.")
async def music_queue_export_slash(interaction: discord.Interaction):
    guild_id = interaction.guild.id; full_queue = []
    if client._current_song.get(guild_id): full_queue.append(client._current_song[guild_id].copy())
    full_queue.extend(s.copy() for s in client._queues.get(guild_id, []))
    if not full_queue:
        await send_custom_response(interaction, embed=create_error_embed("Queue is empty. Nothing to export."), ephemeral_preference=True); return
    urls = [s.get('webpage_url') for s in full_queue if s.get('webpage_url')]
    if not urls:
        await send_custom_response(interaction, embed=create_error_embed("No exportable URLs found in the queue."), ephemeral_preference=True); return
    
    file_obj = StringIO("\n".join(urls))
    fname = "".join(c if c.isalnum() else "_" for c in interaction.guild.name)
    df = discord.File(fp=file_obj, filename=f"{fname}_queue_export.txt")
    await send_custom_response(interaction, content=f"Exported queue with {len(urls)} songs:", embed=None, ephemeral_preference=True) # Send info first
    await interaction.followup.send(file=df, ephemeral=True) # Send file in followup


@music_queue_group.command(name="import", description="Imports songs from a raw text file URL.")
@app_commands.describe(url="URL of raw text file (each line a song URL).", mode="Append or Replace.")
@app_commands.choices(mode=[app_commands.Choice(name="Append", value="append"), app_commands.Choice(name="Replace", value="replace")])
async def music_queue_import_slash(interaction: discord.Interaction, url: str, mode: app_commands.Choice[str]): await _handle_queue_import_logic(interaction, url, mode.value)

@music_settings_group.command(name="volume", description="Sets default music volume (0-200%).")
@app_commands.describe(level="Volume level (e.g., 50 for 50%).")
async def music_settings_volume_slash(interaction: discord.Interaction, level: app_commands.Range[int, 0, 200]): await _handle_settings_volume_logic(interaction, level)

@music_settings_group.command(name="loop", description="Sets default loop mode.")
@app_commands.choices(mode=[app_commands.Choice(name="Off", value="off"), app_commands.Choice(name="Song", value="song"), app_commands.Choice(name="Queue", value="queue")])
async def music_settings_loop_slash(interaction: discord.Interaction, mode: app_commands.Choice[str]): await _handle_settings_loop_logic(interaction, mode.value)

@music_settings_group.command(name="autoplay", description="Toggle default smart autoplay.")
@app_commands.choices(status=[app_commands.Choice(name="On", value="on"), app_commands.Choice(name="Off", value="off")])
async def music_settings_autoplay_slash(interaction: discord.Interaction, status: app_commands.Choice[str]): await _handle_settings_autoplay_logic(interaction, status.value == "on")

@music_settings_group.command(name="247", description="Toggle 24/7 mode (bot stays in VC, auto-plays genre if set).")
@app_commands.choices(status=[app_commands.Choice(name="On", value="on"), app_commands.Choice(name="Off", value="off")])
async def music_settings_247_slash(interaction: discord.Interaction, status: app_commands.Choice[str]): await _handle_settings_247_logic(interaction, status.value == "on")

@music_settings_group.command(name="autoplaygenre", description="Set genre for 24/7 autoplay (e.g., 'Lo-fi', 'Synthwave').")
@app_commands.describe(genre="Genre name, or 'clear' to disable genre-specific autoplay.")
async def music_settings_autoplaygenre_slash(interaction: discord.Interaction, genre: str): await _handle_settings_autoplaygenre_logic(interaction, genre)

@music_settings_group.command(name="djrole", description="Set or clear the DJ role for this server (Admin only).")
@app_commands.describe(role_name_id_mention_or_clear="Role (name, ID, @mention) to set as DJ, or type 'clear' to remove.") # Updated description
async def music_settings_djrole_slash(interaction: discord.Interaction, role_name_id_mention_or_clear: str): # Type hint changed to str
    await _handle_settings_djrole_logic(interaction, role_name_id_mention_or_clear)


@music_settings_group.command(name="view", description="View current saved music settings for this server.")
async def music_settings_view_slash(interaction: discord.Interaction): await _handle_settings_view_logic(interaction)

EFFECT_CHOICES = [
    app_commands.Choice(name="Clear (Default Loudnorm)", value="clear"), app_commands.Choice(name="Raw (No Filters)", value="raw"),
    app_commands.Choice(name="Bass Boost (Low)", value="bass_low"), app_commands.Choice(name="Bass Boost (Medium)", value="bass_medium"),
    app_commands.Choice(name="Bass Boost (High)", value="bass_high"),
    app_commands.Choice(name="Vocal Boost", value="vocal_boost"), app_commands.Choice(name="Treble Boost", value="treble_boost"),
    app_commands.Choice(name="Nightcore", value="nightcore"), app_commands.Choice(name="Vaporwave", value="vaporwave"),
    app_commands.Choice(name="Karaoke (Attempt)", value="karaoke"),
    app_commands.Choice(name="Pitch Up (+1 Semi)", value="pitch_up"), app_commands.Choice(name="Pitch Down (-1 Semi)", value="pitch_down"),
    app_commands.Choice(name="Slowed Tempo", value="slowed_tempo"), app_commands.Choice(name="Sped Up Tempo", value="spedup_tempo"),
    app_commands.Choice(name="Reverb (Small)", value="reverb_small"), app_commands.Choice(name="Reverb (Large)", value="reverb_large"),
]
@effects_group.command(name="apply", description="Apply preset audio effect (saved as default). Restarts song.")
@app_commands.choices(effect=EFFECT_CHOICES)
async def effects_apply_slash(interaction: discord.Interaction, effect: app_commands.Choice[str]): await _handle_effects_apply_logic(interaction, effect.value)

@effects_group.command(name="custom", description="Apply custom FFmpeg filters (saved, ADVANCED). Restarts song.")
@app_commands.describe(filter_string="Raw FFmpeg -af string. 'clear' for default, 'raw' for none.")
async def effects_custom_slash(interaction: discord.Interaction, filter_string: str): await _handle_effects_custom_logic(interaction, filter_string)

@controller_group.command(name="transfer", description="Transfer primary control to another user.")
@app_commands.describe(member="The member to transfer primary control to.")
async def controller_transfer_slash(interaction: discord.Interaction, member: discord.Member): await _handle_controller_transfer_logic(interaction, member)
@controller_group.command(name="add", description="Add user as additional session controller.")
@app_commands.describe(member="The member to add as a controller.")
async def controller_add_slash(interaction: discord.Interaction, member: discord.Member): await _handle_controller_add_logic(interaction, member)
@controller_group.command(name="remove", description="Remove user's additional controller permissions.")
@app_commands.describe(member="The member to remove from controllers.")
async def controller_remove_slash(interaction: discord.Interaction, member: discord.Member): await _handle_controller_remove_logic(interaction, member)
@controller_group.command(name="list", description="Lists current session controllers.")
async def controller_list_slash(interaction: discord.Interaction): await _handle_controller_list_logic(interaction)

@playlist_group.command(name="save", description="Saves current queue as a personal playlist.")
@app_commands.describe(name="Name for new playlist (1-50 chars).")
async def playlist_save_slash(interaction: discord.Interaction, name: str): await _handle_playlist_save_logic(interaction, name)
@playlist_group.command(name="load", description="Loads saved playlist into server queue.")
@app_commands.describe(name="Name of the playlist to load.")
@app_commands.choices(mode=[app_commands.Choice(name="Append", value="append"), app_commands.Choice(name="Replace", value="replace")])
async def playlist_load_slash(interaction: discord.Interaction, name: str, mode: app_commands.Choice[str]): await _handle_playlist_load_logic(interaction, name, mode.value)
@playlist_group.command(name="list", description="Lists your saved personal playlists.")
async def playlist_list_slash(interaction: discord.Interaction): await _handle_playlist_list_logic(interaction)
@playlist_group.command(name="delete", description="Deletes one of your saved personal playlists.")
@app_commands.describe(name="Name of the playlist to delete.")
async def playlist_delete_slash(interaction: discord.Interaction, name: str): await _handle_playlist_delete_logic(interaction, name)

# --- UTILITY SLASH COMMANDS ---
@client.tree.command(name="stats", description="Shows bot statistics.")
async def stats_command(interaction: discord.Interaction):
    delta = datetime.datetime.now(timezone.utc) - client.start_time; days, rem = divmod(int(delta.total_seconds()), 86400); hours, rem = divmod(rem, 3600); mins, secs = divmod(rem, 60)
    uptime = f"{days}d {hours}h {mins}m {secs}s"; playing_now = len([s for s in client._current_song.values() if s])
    queued = sum(len(q) for q in client._queues.values())
    embed = discord.Embed(title=f"{client.user.name} Stats", color=discord.Color.gold(), timestamp=datetime.datetime.now(timezone.utc))
    if client.user.display_avatar: embed.set_thumbnail(url=client.user.display_avatar.url)
    embed.add_field(name="🏓 Latency", value=f"`{round(client.latency*1000)}ms`").add_field(name="⏳ Uptime", value=uptime).add_field(name="💻 Servers", value=str(len(client.guilds)))
    embed.add_field(name="🎤 Active VCs", value=str(len(client._voice_clients))).add_field(name="🎵 Playing/Queued", value=f"{playing_now}/{queued}")
    embed.add_field(name="⚙️ discord.py", value=discord.__version__)
    await send_custom_response(interaction, embed=embed, ephemeral_preference=False)


@client.tree.command(name="clear", description="Clears messages (Mod only).")
@app_commands.describe(amount="Number of messages (1-100).")
@app_commands.checks.has_permissions(manage_messages=True)
async def clear_command_slash(interaction: discord.Interaction, amount: app_commands.Range[int, 1, 100]):
    await interaction.response.defer(ephemeral=True, thinking=True) # Defer must be first
    if not isinstance(interaction.channel, discord.TextChannel):
        await interaction.followup.send("This command can only be used in server text channels.", ephemeral=True); return
    deleted = await interaction.channel.purge(limit=amount)
    await interaction.followup.send(f"🗑️ Deleted {len(deleted)} message(s).", ephemeral=True)


@client.tree.command(name="customprefix", description="Manage custom text command prefixes for this server (Admin).")
@app_commands.checks.has_permissions(manage_guild=True)
@app_commands.describe(action="Action.", prefixes_str="Prefixes (space-separated, e.g., '! ; m!') Max 5 chars/prefix.")
@app_commands.choices(action=[app_commands.Choice(name="List", value="view"), app_commands.Choice(name="Add", value="add"), app_commands.Choice(name="Remove", value="remove"), app_commands.Choice(name="Reset", value="reset")])
async def customprefix_slash_command(interaction: discord.Interaction, action: app_commands.Choice[str], prefixes_str: Optional[str] = None):
    if not interaction.guild:
        await send_custom_response(interaction, content="This command can only be used in a server.", ephemeral_preference=True); return
    guild_id = interaction.guild.id; current_guild_prefixes = client.custom_prefixes.get(guild_id, [client.default_prefix_val])
    if action.value == "view":
        await send_custom_response(interaction, content=f"Current prefixes for this server: `{'`, `'.join(current_guild_prefixes)}`\nDefault bot prefix: `{client.default_prefix_val}`", ephemeral_preference=True); return
    if action.value == "reset":
        if guild_id in client.custom_prefixes: del client.custom_prefixes[guild_id]; await client.save_custom_prefixes_to_file()
        await send_custom_response(interaction, content=f"Custom prefixes reset. Current prefix is now the default: `{client.default_prefix_val}`", ephemeral_preference=True); return
    if not prefixes_str:
        await send_custom_response(interaction, embed=create_error_embed("You must provide prefix(es) for 'add' or 'remove' actions."), ephemeral_preference=True); return
    
    input_prefixes = [p.strip() for p in prefixes_str.split() if p.strip()]
    if not input_prefixes:
        await send_custom_response(interaction, embed=create_error_embed("No valid prefixes provided."), ephemeral_preference=True); return
    
    client.custom_prefixes.setdefault(guild_id, list(current_guild_prefixes))
    modified = False; feedback_prefixes = []
    
    if action.value == "add":
        for p_add in input_prefixes:
            if len(p_add) > 5 : await send_custom_response(interaction, embed=create_error_embed(f"Prefix '{p_add}' is too long (max 5 characters)."), ephemeral_preference=True); return
            if " " in p_add: await send_custom_response(interaction, embed=create_error_embed(f"Prefix '{p_add}' cannot contain spaces."), ephemeral_preference=True); return
            if p_add not in client.custom_prefixes[guild_id]:
                if len(client.custom_prefixes[guild_id]) < 5: client.custom_prefixes[guild_id].append(p_add); feedback_prefixes.append(p_add); modified = True
                else: await send_custom_response(interaction, embed=create_error_embed("Maximum of 5 custom prefixes allowed."), ephemeral_preference=True); break
        msg_action = f"Added prefixes: `{', '.join(feedback_prefixes)}`." if modified and feedback_prefixes else "No new prefixes were added (either duplicates or max reached)."
    elif action.value == "remove":
        for p_rem in input_prefixes:
            if p_rem in client.custom_prefixes[guild_id]:
                if len(client.custom_prefixes[guild_id]) == 1 and p_rem == client.default_prefix_val :
                     await send_custom_response(interaction, embed=create_error_embed(f"Cannot remove the default prefix (`{client.default_prefix_val}`) if it's the only one active. Reset or add another first."), ephemeral_preference=True); return
                client.custom_prefixes[guild_id].remove(p_rem); feedback_prefixes.append(p_rem); modified = True
        if modified and not client.custom_prefixes[guild_id]: client.custom_prefixes.pop(guild_id) # Should not happen due to check above, but safeguard
        msg_action = f"Removed prefixes: `{', '.join(feedback_prefixes)}`." if modified and feedback_prefixes else "No matching prefixes found to remove."
    
    if modified: await client.save_custom_prefixes_to_file()
    final_prefixes_display = client.custom_prefixes.get(guild_id, [client.default_prefix_val])
    await send_custom_response(interaction, content=f"{msg_action}\nCurrent prefixes: `{'`, `'.join(final_prefixes_display)}`", ephemeral_preference=True)


@client.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    msg_content = "An unexpected error occurred with this command."; ephemeral_send = True
    if isinstance(error, app_commands.CommandOnCooldown): msg_content = f"This command is on cooldown! Please try again in {error.retry_after:.2f} seconds."
    elif isinstance(error, app_commands.MissingPermissions): msg_content = f"You are missing the required permissions to use this command: {', '.join(error.missing_permissions)}"
    elif isinstance(error, app_commands.BotMissingPermissions): msg_content = f"I am missing the required permissions to perform this action: {', '.join(error.missing_permissions)}"; ephemeral_send = False # Bot missing perms should be visible
    elif isinstance(error, app_commands.CheckFailure) and ("is_controller" in str(error).lower() or "not client.is_controller" in str(error).lower()): msg_content = "This command can only be used by a session controller or an administrator."
    elif isinstance(error, app_commands.NoPrivateMessage): msg_content = "This command cannot be used in private messages."
    elif isinstance(error, app_commands.CommandInvokeError):
        original = error.original
        print(f"Slash command '{interaction.command.name if interaction.command else 'Unknown'}' raised an exception: {original}", file=sys.stderr); traceback.print_exception(type(original), original, original.__traceback__, file=sys.stderr)
        msg_content = f"An error occurred while executing the command: {truncate_text(str(original), 150)}"
    else: print(f"An unhandled application command error of type {type(error)} occurred: {error}", file=sys.stderr); msg_content = f"An application command error occurred: {truncate_text(str(error), 150)}"
    
    try:
        # Use send_custom_response for consistent handling
        await send_custom_response(interaction, embed=create_error_embed(msg_content), ephemeral_preference=ephemeral_send)
    except Exception as e_send:
        print(f"CRITICAL: Failed to send error message for an application command error: {e_send}", file=sys.stderr)


@client.tree.command(name="help", description="Shows bot and command info.")
async def help_slash_command(interaction: discord.Interaction):
    embed = discord.Embed(title=f"🎧 {client.user.name} Help", description="Advanced Music Bot with persistent settings, effects, and interactive controls.", color=discord.Color.blue())
    if client.user.display_avatar: embed.set_thumbnail(url=client.user.display_avatar.url)
    base = "/music"
    play_cmds = f"`{base} play [query/url]`\n`{base} lyrics [song_title]`"
    ctrl_cmds = f"`{base} controls` `join`, `leave`, `skip`, `voteskip`, `stop`, `pause`, `resume`, `nowplaying`, `seek [time]`"
    q_cmds = f"`{base} queue` `view`, `clear`, `remove [id/title]`, `removerange [s] [e]`, `shuffle`, `move [f] [t]`, `jump [id/title]`, `export`, `import [url] [mode]`"
    set_cmds = f"`{base} settings` `volume [0-200]`, `loop [off|song|q]`, `autoplay [on|off]`, `247 [on|off]`, `autoplaygenre [genre|clear]`, `djrole [<role>|clear]`, `view`"
    eff_cmds = f"`{base} effects` `apply [name]`, `custom [ffmpeg_str]`"
    ctrller_cmds = f"`{base} controller` `list`, `add [@user]`, `remove [@user]`, `transfer [@user]`"
    pl_cmds = f"`{base} playlist` `save [name]`, `load [name] [mode]`, `list`, `delete [name]`"
    embed.add_field(name="🎶 Playback & Lyrics", value=play_cmds, inline=False).add_field(name="⏯️ Controls", value=ctrl_cmds, inline=False)
    embed.add_field(name="🎶 Queue", value=q_cmds, inline=False).add_field(name="⚙️ Settings", value=set_cmds, inline=False) # Corrected field name
    embed.add_field(name="✨ Effects", value=eff_cmds, inline=False).add_field(name="👑 Controllers", value=ctrller_cmds, inline=False)
    embed.add_field(name="📋 Playlists", value=pl_cmds, inline=False)
    embed.add_field(name="🛠️ Utility", value="`/stats`, `/ping`, `/clear [amt]`, `/customprefix [act] [val]`", inline=False)
    pfx = client.custom_prefixes.get(interaction.guild_id, [client.default_prefix_val])[0] if interaction.guild else client.default_prefix_val
    embed.set_footer(text=f"Text commands prefix: `{pfx}` or @Mention. Controllers (joiner/admin/DJ/added) can use restricted commands.")
    await send_custom_response(interaction, embed=embed, ephemeral_preference=True) # Help is usually ephemeral

@client.tree.command(name="ping", description="Check bot's latency.")
async def ping_slash_command(interaction: discord.Interaction):
    await send_custom_response(interaction, content=f"🏓 Pong! Bot latency is `{round(client.latency*1000)}ms`.", ephemeral_preference=True)

# --- SHARED LOGIC IMPLEMENTATIONS ---
# Assuming this is a GLOBAL function, as per your "SHARED LOGIC IMPLEMENTATIONS" comment.
# It requires the 'client_instance' (your MyClient bot instance) to be passed to it.
# Ensure helper functions (send_custom_response, create_error_embed, truncate_text, format_duration)
# and classes (SearchResultsView) and the get_audio_stream_info function are defined and accessible.

# Assumes this is a global function taking 'client_instance' as the first argument.

async def _handle_play_logic(
    client_instance: 'MyClient', 
    ctx_or_interaction: Union[commands.Context, discord.Interaction], 
    query: str, 
    platform_override: Optional[str] = None,
    original_text_query: Optional[str] = None
):
    print(f"\nDEBUG CMD_PLAY: _handle_play_logic CALLED. Query: '{truncate_text(query, 100)}', Platform Override: {platform_override}")
    
    # --- NEW: Spotify Check ---
    # If a Spotify link somehow reaches this function, it means the on_message embed handler failed.
    # We will explicitly NOT process it here to avoid the DRM error.
    if "open.spotify.com/" in query.lower():
        print("DEBUG CMD_PLAY: Spotify link received. The on_message embed handler should have caught this. It likely failed to get an embed. Ignoring command.")
        await send_custom_response(ctx_or_interaction, 
                                   embed=create_error_embed("Failed to process Spotify link. This can happen if Discord fails to generate a link preview (embed). Please try sending the link again."),
                                   ephemeral_preference=True)
        return
    # --- END NEW SPOTIFY CHECK ---

    # The rest of the function proceeds exactly as before, but without the `if is_spotify_query:` block.
    # It now only handles direct URLs (non-Spotify) and search queries (YouTube/SoundCloud).

    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    # ... (guild, user, channel setup) ...
    guild = ctx_or_interaction.guild; guild_id = guild.id; user_obj = ctx_or_interaction.user if is_interaction else ctx_or_interaction.author; text_channel_for_feedback = ctx_or_interaction.channel

    if is_interaction and platform_override is None and original_text_query is None: 
        if not ctx_or_interaction.response.is_done(): await ctx_or_interaction.response.defer(thinking=True)
    elif not is_interaction: await ctx_or_interaction.typing()

    vc = await client_instance.ensure_voice_client(ctx_or_interaction, join_if_not_connected=True)
    if not vc: return

    # ... (the rest of your _handle_play_logic, starting from the prefix parsing for sc:/yt:) ...
    # ... It should NOT contain the `if is_spotify_query:` block anymore.
    # (Copied from previous full version, with the Spotify block removed)
    current_query_for_search = original_text_query if original_text_query else query
    is_url = re.match(r"https?://[^\s]+", current_query_for_search) is not None
    search_platform = platform_override if platform_override else "youtube" 
    actual_search_query_for_provider = current_query_for_search 
    is_prefixed_search = False 
    if platform_override is None and original_text_query is None:
        if query.lower().startswith("sc:") or query.lower().startswith("soundcloud:"):
            search_platform = "soundcloud"; actual_search_query_for_provider = re.sub(r"^(sc:|soundcloud:)\s*", "", query, flags=re.IGNORECASE).strip(); current_query_for_search = actual_search_query_for_provider; is_url = False; is_prefixed_search = True
        elif query.lower().startswith("yt:") or query.lower().startswith("youtube:"):
            search_platform = "youtube"; actual_search_query_for_provider = re.sub(r"^(yt:|youtube:)\s*", "", query, flags=re.IGNORECASE).strip(); current_query_for_search = actual_search_query_for_provider; is_url = False; is_prefixed_search = True
    elif platform_override:
        search_platform = platform_override; actual_search_query_for_provider = current_query_for_search; is_url = False; is_prefixed_search = True
    elif original_text_query:
        actual_search_query_for_provider = current_query_for_search; is_url = False; is_prefixed_search = True

    song_audio_info = None
    
    if not is_url or is_prefixed_search: 
        # ... (All of your general search logic for both slash and text commands, exactly as before) ...
        # (This block is long, but it's the same code you already have)
        query_to_use_for_this_search_internally = actual_search_query_for_provider
        platform_display_name = search_platform.capitalize()
        # ... (rest of the combined search logic from the previous answer) ...
        # Ensure that it correctly sets `song_audio_info` after a selection, or returns if no selection.
        if not query_to_use_for_this_search_internally:
             song_audio_info = {"error": f"Search query for {platform_display_name} cannot be empty.", "title": query}
        elif is_interaction: 
            # (Slash command search logic with SearchResultsView and platform switch)
            search_results_data = await get_audio_stream_info(query_to_use_for_this_search_internally, search=True, search_results_count=MAX_SEARCH_RESULTS, search_provider=search_platform)
            # ... (the rest of the slash command search path from previous answer)
            if not search_results_data or "error" in search_results_data or not search_results_data.get('entries'):
                err_msg = search_results_data.get('error', "No results found.") if search_results_data else "No results found."
                await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Search on {platform_display_name} for '{query_to_use_for_this_search_internally}' failed: {err_msg}"), ephemeral_preference=True); return
            original_response_message_obj = None #... (get original response message)
            if ctx_or_interaction.response.is_done():
                try: original_response_message_obj = await ctx_or_interaction.original_response()
                except discord.HTTPException: pass
            search_view_instance = SearchResultsView(interaction=ctx_or_interaction, results=search_results_data['entries'], original_query=query_to_use_for_this_search_internally, current_platform=search_platform, parent_message_id=original_response_message_obj.id if original_response_message_obj else None)
            embed_search = discord.Embed(title=f"🔎 {platform_display_name} Search Results for '{query_to_use_for_this_search_internally}'", description="Select an item or switch platform:", color=discord.Color.gold())
            if platform_override and original_response_message_obj: 
                 try: await original_response_message_obj.edit(embed=embed_search, view=search_view_instance, content=None)
                 except discord.HTTPException as e: await send_custom_response(ctx_or_interaction, embed=embed_search, view=search_view_instance, ephemeral_preference=False)
            else: await send_custom_response(ctx_or_interaction, embed=embed_search, view=search_view_instance, ephemeral_preference=False)
            await search_view_instance.wait()
            if search_view_instance.switched_platform:
                new_platform = "soundcloud" if search_platform == "youtube" else "youtube"
                await _handle_play_logic(client_instance, ctx_or_interaction, search_view_instance.original_query, platform_override=new_platform, original_text_query=None) # Pass client_instance
                return 
            if search_view_instance.selected_song_info:
                selected_url = search_view_instance.selected_song_info.get('webpage_url') or search_view_instance.selected_song_info.get('url')
                if selected_url: song_audio_info = await get_audio_stream_info(selected_url, search=False)
                else: song_audio_info = {"error": "Selected search result missing a valid URL."}
            else: return

        else: # (Text command search logic with SoundCloud switch)
            # ... (The full text search logic from previous answer goes here)
            search_results_data = await get_audio_stream_info(query_to_use_for_this_search_internally, search=True, search_results_count=MAX_SEARCH_RESULTS, search_provider=search_platform)
            # (Your full text search logic here to select an item and set song_audio_info, including the recursive call for SoundCloud switch)
            if not search_results_data or "error" in search_results_data or not search_results_data.get('entries'):
                err_msg = search_results_data.get('error', "No results found.") if search_results_data else "No results found."
                await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Search on {platform_display_name} for '{query_to_use_for_this_search_internally}' failed: {err_msg}"), ephemeral_preference=False); return
            results_to_display = search_results_data['entries'][:min(len(search_results_data['entries']), 5)]
            if not results_to_display:
                await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"No displayable results for '{query_to_use_for_this_search_internally}' on {platform_display_name}."), ephemeral_preference=False); return
            embed_text_search = discord.Embed(title=f"🔎 {platform_display_name} Search Results for '{query_to_use_for_this_search_internally}'", color=discord.Color.gold())
            # ... (populate embed) ...
            desc_lines, reaction_emojis_select, reaction_emoji_switch_sc = [], ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣"], "☁️"
            for i, res in enumerate(results_to_display): desc_lines.append(f"{reaction_emojis_select[i]} **{i+1}.** {truncate_text(res.get('title','N/A'), 60)} ({format_duration(res.get('duration'))})")
            embed_text_search.description = "\n".join(desc_lines)
            footer_text = "React with number to select (30s timeout). Type 'cancel' to abort."
            can_switch_to_soundcloud = (search_platform == "youtube" and not original_text_query)
            if can_switch_to_soundcloud: footer_text += f"\nReact with {reaction_emoji_switch_sc} to search on SoundCloud instead."
            embed_text_search.set_footer(text=footer_text)
            search_msg_obj = await text_channel_for_feedback.send(embed=embed_text_search)
            # ... (add reactions)
            active_reactions_for_wait = []
            for i in range(len(results_to_display)): await search_msg_obj.add_reaction(reaction_emojis_select[i]); active_reactions_for_wait.append(reaction_emojis_select[i])
            if can_switch_to_soundcloud: await search_msg_obj.add_reaction(reaction_emoji_switch_sc); active_reactions_for_wait.append(reaction_emoji_switch_sc)
            client_instance._pending_text_searches[user_obj.id] = { # ... (store pending)
                'message_id': search_msg_obj.id, 'results': results_to_display, 
                'timestamp': datetime.datetime.now(timezone.utc), 'channel_id': text_channel_for_feedback.id,
                'requester_mention': user_obj.mention,
                'original_query_for_switch': query_to_use_for_this_search_internally 
            }
            # ... (wait_for logic)
            chosen_idx = -1; switch_triggered = False; reaction_task = None; message_task = None
            try:
                # ... (check definitions)
                react_check_text_search = lambda r, u: u == user_obj and r.message.id == search_msg_obj.id and str(r.emoji) in active_reactions_for_wait
                msg_check_text_search = lambda m: m.author == user_obj and m.channel == text_channel_for_feedback and \
                                   (m.content.lower() == 'cancel' or (m.content.isdigit() and 1 <= int(m.content) <= len(results_to_display)))
                reaction_task = asyncio.create_task(client_instance.wait_for('reaction_add', timeout=30.0, check=react_check_text_search))
                message_task = asyncio.create_task(client_instance.wait_for('message', timeout=30.0, check=msg_check_text_search))
                # ... (await wait)
                done, pending = await asyncio.wait([reaction_task, message_task], return_when=asyncio.FIRST_COMPLETED)
                for future in done: # ...
                    if future.exception() is None:
                        event_res = future.result()
                        if isinstance(event_res, tuple) and len(event_res) > 0 and isinstance(event_res[0], discord.Reaction):
                            emoji_str = str(event_res[0].emoji)
                            if emoji_str == reaction_emoji_switch_sc and can_switch_to_soundcloud: switch_triggered = True
                            elif emoji_str in reaction_emojis_select: chosen_idx = reaction_emojis_select.index(emoji_str)
                        elif isinstance(event_res, discord.Message):
                            if event_res.content.lower() == 'cancel': chosen_idx = -2
                            else: chosen_idx = int(event_res.content) - 1
                            try: await event_res.delete(delay=0.5)
                            except: pass
                        break 
                for fut_pend in pending: fut_pend.cancel()
            except: pass 
            finally: # ...
                if reaction_task and not reaction_task.done(): reaction_task.cancel()
                if message_task and not message_task.done(): message_task.cancel()
            pending_data = client_instance._pending_text_searches.pop(user_obj.id, None)
            if switch_triggered: # ... (handle switch)
                original_query_from_pending = pending_data['original_query_for_switch'] if pending_data else query_to_use_for_this_search_internally
                try: 
                    await search_msg_obj.edit(content=f"Switching search to SoundCloud for '{original_query_from_pending}'...", embed=None, view=None)
                    await search_msg_obj.clear_reactions()
                except discord.HTTPException: pass
                await _handle_play_logic(client_instance, ctx_or_interaction, original_query_from_pending, platform_override="soundcloud", original_text_query=original_query_from_pending)
                return 
            # ... (handle selection, cancel, timeout)
            if chosen_idx == -2: # Copied
                try: await search_msg_obj.edit(content="Search cancelled.", embed=None, view=None); await search_msg_obj.clear_reactions()
                except: pass
                return
            if chosen_idx != -1 and pending_data: # Copied
                selected_ref = pending_data['results'][chosen_idx]
                sel_url = selected_ref.get('webpage_url') or selected_ref.get('url')
                if sel_url: song_audio_info = await get_audio_stream_info(sel_url, search=False) 
                else: song_audio_info = {"error": "Selected text search result missing URL."}
                try: 
                    title_display = song_audio_info.get('title','N/A') if song_audio_info and "error" not in song_audio_info else "Error"
                    await search_msg_obj.edit(content=f"Selected: **{truncate_text(title_display, 60)}** from {platform_display_name}.\nAdding to queue...", embed=None, view=None); await search_msg_obj.clear_reactions()
                except: pass
            else: # Copied
                try: await search_msg_obj.edit(content="Search timed out/invalid.", embed=None, view=None); await search_msg_obj.clear_reactions()
                except: pass
                return


    elif is_url: # Direct URL (but guaranteed not Spotify at this point)
        song_audio_info = await get_audio_stream_info(query, search=False)

    # ... (Common queuing logic at the end - this part is unchanged and required)
    if not song_audio_info or "error" in song_audio_info or not song_audio_info.get('webpage_url'):
        err_msg = song_audio_info['error'] if song_audio_info and 'error' in song_audio_info else "Could not process the provided link or query."
        title_err_context = original_text_query if original_text_query else query 
        if song_audio_info and song_audio_info.get("title"): title_err_context = song_audio_info.get("title")
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Failed to add '{truncate_text(title_err_context,70)}': {err_msg}"), ephemeral_preference=True)
        return

    client_instance._queues.setdefault(guild_id, [])
    if len(client_instance._queues[guild_id]) >= MAX_QUEUE_SIZE:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Queue is full ({MAX_QUEUE_SIZE} songs)."), ephemeral_preference=True); return
    
    song_to_add = {
        'webpage_url': song_audio_info.get('webpage_url'), 'title': song_audio_info.get('title', 'Unknown Title'),
        'duration': song_audio_info.get('duration'), 'thumbnail': song_audio_info.get('thumbnail'),
        'uploader': song_audio_info.get('uploader', 'Unknown Uploader'), 'requester': user_obj.mention,
        'stream_url': song_audio_info.get('url')
    }
    client_instance._queues[guild_id].append(song_to_add)
    await client_instance.save_guild_settings_to_file(guild_id) 
    
    add_embed = discord.Embed(title="🎵 Added to Queue", description=f"[{truncate_text(song_to_add['title'],70)}]({song_to_add['webpage_url']})", color=discord.Color.green())
    add_embed.add_field(name="Position", value=str(len(client_instance._queues[guild_id])))
    add_embed.add_field(name="Duration", value=format_duration(song_to_add['duration']))
    if song_to_add.get('thumbnail'): add_embed.set_thumbnail(url=song_to_add['thumbnail'])
    await send_custom_response(ctx_or_interaction, embed=add_embed, ephemeral_preference=False)
    
    if not vc.is_playing() and not client_instance._current_song.get(guild_id) and client_instance._queues.get(guild_id):
        await client_instance._play_guild_queue(guild_id)
    elif guild_id in client_instance._leave_tasks: 
        client_instance._leave_tasks[guild_id].cancel(); client_instance._leave_tasks.pop(guild_id, None)

async def _handle_skip_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    # Ensure guild is available
    guild = ctx_or_interaction.guild
    if not guild:
        # This should ideally not happen for guild-based music commands
        if is_interaction: await send_custom_response(interaction, embed=create_error_embed("This command can only be used in a server."), ephemeral_preference=True)
        else: await send_custom_response(ctx_or_interaction, embed=create_error_embed("This command can only be used in a server."), ephemeral_preference=False)
        return
        
    guild_id = guild.id
    user_obj = ctx_or_interaction.user if is_interaction else ctx_or_interaction.author
    
    current_song_data = client._current_song.get(guild_id) # Fetch current song for checks
    is_requester = False
    if current_song_data and current_song_data.get('requester'):
        # Robust requester check by ID
        match = re.match(r"<@!?(\d+)>", current_song_data['requester'])
        if match:
            requester_id = int(match.group(1))
            is_req = (user_obj.id == requester_id)
        elif current_song_data['requester'] == user_obj.mention: # Fallback
            is_req = True


    if not client.is_controller(ctx_or_interaction) and not is_requester: # Corrected is_req
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need to be a controller or the song requester to skip."), ephemeral_preference=True)
        return

    vc = client._voice_clients.get(guild_id)
    # Re-fetch current_song_for_title in case it changed due to concurrent action
    # (though less likely for a skip initiated by user action)
    current_song_for_title_display = client._current_song.get(guild_id) 
    if not vc or not vc.is_connected() or not current_song_for_title_display:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Not playing anything to skip."), ephemeral_preference=True)
        return

    skipped_title = current_song_for_title_display.get('title', 'Current song')
    
    # --- KEY CHANGE FOR LOOP OVERRIDE ---
    # Temporarily set a flag or modify state so _handle_after_play knows this was an explicit skip
    # One simple way: If loop mode is 'song', change it to 'off' *before* stopping.
    # _handle_after_play will then not replay it. The original loop mode is saved in settings.
    # This assumes _handle_after_play always reads the *current runtime* loop mode.
    
    original_loop_mode = client.get_guild_loop_mode(guild_id)
    was_song_loop = (original_loop_mode == "song")
    
    if was_song_loop:
        print(f"DEBUG SKIP: Song loop was on. Temporarily setting loop to 'off' for skip.")
        # We don't call set_guild_loop_mode here because that saves it as the new default.
        # Instead, we'll handle this in _handle_after_play by checking if a skip was forced.
        # A simpler way for now: _handle_after_play checks if _is_processing_next_song is False.
        # If it's False (meaning skip was called before song naturally ended), it should not honor song loop.
        # For an explicit skip, we want to bypass the "loop song" logic in _handle_after_play.
        # The easiest way is to ensure that when vc.stop() is called, _handle_after_play
        # can differentiate between a natural end and a forced stop.
        # We can set a temporary attribute on the client for this guild.
        setattr(client, f"_skip_forced_{guild_id}", True)


    if guild_id in client._up_next_tasks: client._up_next_tasks[guild_id].cancel(); client._up_next_tasks.pop(guild_id, None)
    
    # client._is_processing_next_song[guild_id] = False # This is set in _play_guild_queue.
                                                     # Forcing it false here might be okay,
                                                     # but let _play_guild_queue manage it.
                                                     # The critical part is vc.stop().
    
    print(f"DEBUG SKIP: Stopping VC for guild {guild_id} to skip '{skipped_title}'")
    vc.stop() # This will trigger the _handle_after_play callback.
    
    # Defer if interaction, as vc.stop() is async and might take a moment for _handle_after_play to kick in.
    if is_interaction and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=False) # Skip message is public

    # The confirmation message is now sent *after* the song has actually been processed by _handle_after_play
    # This makes the UX more accurate.
    # We will send this from the NowPlayingView skip button or the command itself.
    # The `vc.stop()` is the main action.

    # Send confirmation (this is okay to send before _handle_after_play fully completes the next song load)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Song Skipped", f"Skipping **{truncate_text(skipped_title,70)}**..."), ephemeral_preference=False)

async def _handle_stop_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can stop playback."), ephemeral_preference=True); return

    guild_id = ctx_or_interaction.guild.id; vc = client._voice_clients.get(guild_id)
    
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=False) # Stop message is public

    client._queues[guild_id] = []
    client._current_song[guild_id] = None # Clear current song before saving
    client.set_guild_loop_mode(guild_id, "off") # Reset loop on stop
    if guild_id in client._up_next_tasks: client._up_next_tasks[guild_id].cancel(); client._up_next_tasks.pop(guild_id, None)
    client._is_processing_next_song[guild_id] = False
    
    await client.save_guild_settings_to_file(guild_id) # Save cleared queue and loop mode

    if vc and vc.is_connected():
        vc.stop() # Stop playback
        await client.disconnect_voice(guild_id) # Handles full disconnect and cleanup
        msg_embed = discord.Embed(title="⏹️ Playback Stopped", description="Queue cleared, and I've left the voice channel.", color=discord.Color.dark_red())
    else:
        # Bot wasn't in VC, but still clear data and save (disconnect_voice handles this)
        await client.disconnect_voice(guild_id) # Ensure cleanup even if not in VC
        msg_embed = create_info_embed("Session Data Cleared", "Bot was not in a voice channel, but session data (queue, loop) has been reset.")
    
    await send_custom_response(ctx_or_interaction, embed=msg_embed, ephemeral_preference=False)


async def _handle_nowplaying_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    guild_id = ctx_or_interaction.guild.id; current = client._current_song.get(guild_id)
    if not current:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Nothing is currently playing."), ephemeral_preference=True); return
    
    embed = discord.Embed(title="▶️ Now Playing", description=f"[{truncate_text(current['title'],70)}]({current['webpage_url']})", color=discord.Color.blurple())
    if current.get('thumbnail'): embed.set_thumbnail(url=current['thumbnail'])
    
    progress_str = format_duration(current.get('duration', 0))
    if current.get('duration') is not None and current.get('duration') > 0 and not current.get('is_live_stream'):
        elapsed_time_sec = current.get('accumulated_play_time_seconds', 0.0)
        if current.get('play_start_utc'): elapsed_time_sec += (datetime.datetime.now(timezone.utc) - current['play_start_utc']).total_seconds()
        elapsed_time_sec = min(elapsed_time_sec, current['duration'])
        
        bar_len = 20; prog_pct = elapsed_time_sec / current['duration'] if current['duration'] > 0 else 0
        fill_len = int(bar_len * prog_pct)
        bar = ('─' * fill_len + '🔵' + '─' * (bar_len - fill_len -1)) if 0 <= fill_len < bar_len else ('─' * bar_len + '🏁')
        progress_str = f"`{format_duration(elapsed_time_sec)}` {bar} `{format_duration(current['duration'])}`"
    elif current.get('is_live_stream'):
        progress_str = "🔴 LIVE"

    embed.add_field(name="Progress", value=progress_str, inline=False).add_field(name="Requested by", value=current['requester'])
    if current.get('uploader'): embed.add_field(name="Uploader", value=truncate_text(current['uploader'],30))
    embed.add_field(name="Volume", value=f"{int(client.get_guild_volume(guild_id) * 100)}%").add_field(name="Loop", value=client.get_guild_loop_mode(guild_id).capitalize())
    embed.add_field(name="Effects", value=client.get_active_effects_display(guild_id), inline=False)
    await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=False) # NP is public


async def _handle_leave_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can make me leave."), ephemeral_preference=True); return
    
    guild_id = ctx_or_interaction.guild.id; vc = client._voice_clients.get(guild_id)
    
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=False)

    if vc and vc.is_connected():
        client.set_guild_loop_mode(guild_id, "off") # Turn off loop on manual leave
        if vc.is_playing() or vc.is_paused(): vc.stop() # Stop current playback
        if guild_id in client._up_next_tasks: client._up_next_tasks[guild_id].cancel(); client._up_next_tasks.pop(guild_id, None)
        client._is_processing_next_song[guild_id] = False
        
        await client.disconnect_voice(guild_id) # Saves settings and cleans up
        await send_custom_response(ctx_or_interaction, embed=create_info_embed("Disconnected", "I have left the voice channel. The queue is saved if you rejoin."), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("I'm not currently in a voice channel."), ephemeral_preference=True)


async def _handle_pause_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can pause playback."), ephemeral_preference=True); return
    
    guild_id = ctx_or_interaction.guild.id; vc = client._voice_clients.get(guild_id)
    if vc and vc.is_playing():
        vc.pause(); current_song = client._current_song.get(guild_id)
        if current_song and current_song.get('play_start_utc'):
            elapsed_this_segment = (datetime.datetime.now(timezone.utc) - current_song['play_start_utc']).total_seconds()
            current_song['accumulated_play_time_seconds'] = current_song.get('accumulated_play_time_seconds', 0.0) + elapsed_this_segment
            current_song['play_start_utc'] = None; await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_info_embed("Playback Paused ⏸️", "The current song has been paused."), ephemeral_preference=False)
    elif vc and vc.is_paused():
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Playback is already paused."), ephemeral_preference=True)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Nothing is currently playing to pause."), ephemeral_preference=True)

async def _handle_resume_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can resume playback."), ephemeral_preference=True); return
        
    guild_id = ctx_or_interaction.guild.id; vc = client._voice_clients.get(guild_id)
    if vc and vc.is_paused():
        vc.resume(); current_song = client._current_song.get(guild_id)
        if current_song: current_song['play_start_utc'] = datetime.datetime.now(timezone.utc)
        # Don't save yet, other events or next song will handle saving accumulated time update
        await send_custom_response(ctx_or_interaction, embed=create_info_embed("Playback Resumed ▶️", "Playback has been resumed."), ephemeral_preference=False)
    elif vc and vc.is_playing():
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Playback is already in progress."), ephemeral_preference=True)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Nothing is paused or playing."), ephemeral_preference=True)


async def _handle_seek_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], timestamp: str):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can seek."), ephemeral_preference=True); return
        
    guild_id = ctx_or_interaction.guild.id; vc = client._voice_clients.get(guild_id); current = client._current_song.get(guild_id)
    if not vc or not (vc.is_playing() or vc.is_paused()) or not current or current.get('is_live_stream'):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Cannot seek: Not playing, song is live, or no current song."), ephemeral_preference=True); return
    
    seek_seconds = parse_timestamp(timestamp); current_duration = current.get('duration')
    if seek_seconds is None or seek_seconds < 0:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Invalid timestamp format. Use HH:MM:SS, MM:SS, or SS."), ephemeral_preference=True); return
    if current_duration is not None and isinstance(current_duration, (int,float)) and seek_seconds >= current_duration:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Seek time ({format_duration(seek_seconds)}) exceeds song duration ({format_duration(current_duration)})."), ephemeral_preference=True); return
    
    # Defer for interactions as _play_guild_queue involves async operations
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=True) # Ephemeral confirm before public NP

    await send_custom_response(ctx_or_interaction, embed=create_info_embed("Seeking...", f"Attempting to seek to {format_duration(seek_seconds)}."), ephemeral_preference=True)
    
    song_to_replay = current.copy()
    # No need to stop vc explicitly here, _play_guild_queue handles it.
    await client._play_guild_queue(guild_id, song_to_replay=song_to_replay, seek_seconds=seek_seconds)
    # _play_guild_queue will send a new Now Playing message if successful.


async def _handle_lyrics_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], song_title_query: Optional[str] = None):
    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    if is_interaction:
        if not ctx_or_interaction.response.is_done(): await ctx_or_interaction.response.defer(thinking=True, ephemeral=True) # Lyrics can be long, so ephemeral preferred initially
    else: await ctx_or_interaction.typing()
    
    guild_id = ctx_or_interaction.guild.id if ctx_or_interaction.guild else None
    target_title = None; target_artist = None
    if song_title_query: target_title = song_title_query
    elif guild_id and client._current_song.get(guild_id):
        cs = client._current_song[guild_id]; target_title = cs.get('title'); target_artist = cs.get('uploader')
    else:
        err_msg = "Please specify a song title or play a song for me to find lyrics."
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(err_msg), ephemeral_preference=True)
        return

    if not target_title:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("No song title provided for lyrics search."), ephemeral_preference=True)
        return

    lyrics = await fetch_lyrics(target_title, target_artist)
    
    if lyrics and "not found" not in lyrics.lower() and "api error" not in lyrics.lower() and "timed out" not in lyrics.lower() and "could not fetch" not in lyrics.lower() :
        parts = []; max_len = 1980 # Embed description limit is 4096, but individual messages are better shorter
        while len(lyrics) > max_len:
            split_at = lyrics.rfind('\n\n', 0, max_len) if '\n\n' in lyrics[:max_len] else lyrics.rfind('\n', 0, max_len) if '\n' in lyrics[:max_len] else max_len
            parts.append(lyrics[:split_at]); lyrics = lyrics[split_at:].lstrip()
        parts.append(lyrics)
        
        first_message_sent = False
        for i, part_text in enumerate(parts):
            embed = discord.Embed(title=f"🎤 Lyrics for {truncate_text(target_title, 100)}", description=part_text, color=discord.Color.teal())
            if len(parts) > 1: embed.set_footer(text=f"Part {i+1}/{len(parts)}")
            
            # For slash, first part uses followup if deferred, then sends to channel. For text, all go to channel.
            if is_interaction:
                if not first_message_sent:
                    await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=False) # First part public
                    first_message_sent = True
                else: # Subsequent parts always public to channel
                    await ctx_or_interaction.channel.send(embed=embed)
            else:
                await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=False) # Text always public
            if i < len(parts) - 1: await asyncio.sleep(0.5) # Slight delay between parts
    else:
        err_msg_lyrics = lyrics if lyrics else "Lyrics could not be found or an API error occurred."
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Lyrics Search Error: {err_msg_lyrics}"), ephemeral_preference=True)

async def _handle_queue_clear_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can clear the queue."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    if client._queues.get(guild_id):
        client._queues[guild_id] = []; await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Queue Cleared", "All songs have been removed from the queue."), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is already empty."), ephemeral_preference=True)


async def _handle_queue_remove_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], identifier: str):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can remove songs."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id; queue = client._queues.get(guild_id, [])
    if not queue:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is empty."), ephemeral_preference=True); return
    
    removed_song = None
    try:
        idx = int(identifier) - 1
        if 0 <= idx < len(queue): removed_song = queue.pop(idx)
    except ValueError:
        ident_lower = identifier.lower()
        # Search from bottom up so removing multiple by title starts with earlier occurrences
        for i in range(len(queue) -1, -1, -1):
            if ident_lower in queue[i]['title'].lower(): removed_song = queue.pop(i); break 
                
    if removed_song:
        await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Song Removed", f"Removed **{truncate_text(removed_song['title'],60)}** from the queue."), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Could not find a song matching '{identifier}' in the queue."), ephemeral_preference=True)


async def _handle_queue_removerange_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], start_index: int, end_index: int):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can remove a range of songs."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id; queue = client._queues.get(guild_id, [])
    if not queue:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is empty."), ephemeral_preference=True); return

    start_0 = start_index - 1; end_0 = end_index - 1
    if not (0 <= start_0 < len(queue) and start_0 <= end_0 < len(queue)):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Invalid range. Please provide indices between 1 and {len(queue)}."), ephemeral_preference=True); return
    
    num_to_remove = (end_0 - start_0) + 1; removed_count = 0
    # Iteratively pop from the start_0 index. This handles shifting indices.
    for _ in range(num_to_remove):
        if start_0 < len(client._queues[guild_id]): # Check bounds each time
            client._queues[guild_id].pop(start_0)
            removed_count += 1
        else: break # Should not be strictly necessary with initial range check, but safe
    
    if removed_count > 0:
        await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Songs Removed", f"Successfully removed {removed_count} songs from the queue."), ephemeral_preference=False)
    else: # Should not happen if range was valid and queue not empty.
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("No songs were removed. Please check the range."), ephemeral_preference=True)


async def _handle_queue_shuffle_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can shuffle the queue."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    if client._queues.get(guild_id) and len(client._queues[guild_id]) > 1:
        random.shuffle(client._queues[guild_id]); await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=discord.Embed(title="🔀 Queue Shuffled", description="The song queue has been shuffled!", color=discord.Color.random()), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Not enough songs in the queue to shuffle (need at least 2)."), ephemeral_preference=True)


async def _handle_queue_move_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], from_index: int, to_index: int):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can move songs."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id; queue = client._queues.get(guild_id, [])
    if not queue:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is empty."), ephemeral_preference=True); return
    
    from_0 = from_index - 1; to_0 = to_index - 1
    max_idx = len(queue) -1
    # For 'to_index', allow it to be len(queue) (1 after last actual index) to move to end
    if not (0 <= from_0 <= max_idx and 0 <= to_0 <= len(queue)): # to_0 can be len(queue)
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Invalid index. 'From' must be 1-{len(queue)}, 'To' must be 1-{len(queue)+1}."), ephemeral_preference=True); return
    if from_0 == to_0 or (from_0 == max_idx and to_0 == len(queue)): # Trying to move to same spot or last to end
         await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Song is already at or effectively at position {to_index}."), ephemeral_preference=True); return
    
    song_to_move = queue.pop(from_0)
    # If to_0 was intended for the end (len(queue) before pop), it's now one less or simply append
    if to_0 >= len(queue): # After pop, if to_0 was original len(queue) or more
        queue.append(song_to_move)
    else:
        queue.insert(to_0, song_to_move)

    await client.save_guild_settings_to_file(guild_id)
    final_pos = queue.index(song_to_move) + 1 # Get actual new 1-based index
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Song Moved", f"Moved '{truncate_text(song_to_move['title'], 50)}' from position {from_index} to {final_pos}."), ephemeral_preference=False)


async def _handle_queue_jump_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], identifier: str):
    if not client.is_controller(ctx_or_interaction):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only controllers can jump to a song."), ephemeral_preference=True); return
    
    guild_id = ctx_or_interaction.guild.id; queue = client._queues.get(guild_id, []); vc = client._voice_clients.get(guild_id)
    if not queue:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is empty."), ephemeral_preference=True); return
    if not vc or not vc.is_connected():
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("I'm not connected to a voice channel."), ephemeral_preference=True); return
    
    target_song_info = None; target_song_idx_0 = -1
    try: 
        idx_1 = int(identifier); idx_0 = idx_1 - 1
        if 0 <= idx_0 < len(queue): target_song_info = queue[idx_0]; target_song_idx_0 = idx_0
    except ValueError:
        ident_lower = identifier.lower()
        for i, song in enumerate(queue):
            if ident_lower in song['title'].lower(): target_song_info = song; target_song_idx_0 = i; break
    
    if not target_song_info:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Could not find a song matching '{identifier}' in the queue."), ephemeral_preference=True); return
    
    # Defer interaction if not already, as operations below are async
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=False) # Jump confirmation is public

    song_to_jump_to = client._queues[guild_id].pop(target_song_idx_0)
    client._queues[guild_id].insert(0, song_to_jump_to)
    
    if guild_id in client._up_next_tasks: client._up_next_tasks[guild_id].cancel(); client._up_next_tasks.pop(guild_id, None)
    client._is_processing_next_song[guild_id] = False
    
    await send_custom_response(ctx_or_interaction, embed=create_info_embed("Jumped in Queue", f"Skipping to **{truncate_text(target_song_info['title'],60)}**. It will play next."), ephemeral_preference=False)
    
    if vc.is_playing() or vc.is_paused() or client._current_song.get(guild_id): vc.stop() # Trigger next play
    else: await client._play_guild_queue(guild_id) # If bot was idle
    await client.save_guild_settings_to_file(guild_id)

async def _handle_queue_import_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], url: str, mode: str):
    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    if is_interaction:
        if not ctx_or_interaction.response.is_done(): await ctx_or_interaction.response.defer(thinking=True)
    else: await ctx_or_interaction.typing()
    
    guild_id = ctx_or_interaction.guild.id
    user_mention = ctx_or_interaction.user.mention if is_interaction else ctx_or_interaction.author.mention

    vc = await client.ensure_voice_client(ctx_or_interaction, join_if_not_connected=True)
    if not vc: return # Error handled by ensure_voice_client
    
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=10) as resp:
                if resp.status != 200:
                    await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Failed to fetch the URL (Status: {resp.status})."), ephemeral_preference=True); return
                content = await resp.text()
    except Exception as e:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Error fetching URL: {e}"), ephemeral_preference=True); return

    urls_to_add = [line.strip() for line in content.splitlines() if line.strip().startswith("http")]
    if not urls_to_add:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("No valid URLs found in the provided file content."), ephemeral_preference=True); return

    client._queues.setdefault(guild_id, [])
    if mode == "replace":
        client._queues[guild_id] = []
        if client._current_song.get(guild_id): 
            if vc.is_playing() or vc.is_paused(): vc.stop()
            client._current_song[guild_id] = None

    added_count = 0; failed_count = 0
    max_to_add_this_session = 50 # Limit imports per command to avoid abuse/long waits
    initial_queue_size = len(client._queues[guild_id])

    for i, song_url in enumerate(urls_to_add):
        if i >= max_to_add_this_session:
            await send_custom_response(ctx_or_interaction, embed=create_info_embed("Import Limit Reached", f"Imported {added_count} songs. Maximum {max_to_add_this_session} songs can be imported at once."), ephemeral_preference=True); break
        if initial_queue_size + added_count >= MAX_QUEUE_SIZE:
            await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Queue is full. Successfully added {added_count} songs. {failed_count} URLs failed or were skipped."), ephemeral_preference=True); break
        
        temp_requester = f"{user_mention} (Import)" 
        song_audio_info = await get_audio_stream_info(song_url)
        if not song_audio_info or "error" in song_audio_info or not song_audio_info.get('webpage_url'):
            failed_count += 1; continue
        
        client._queues[guild_id].append({
            'webpage_url': song_audio_info.get('webpage_url'), 'title': song_audio_info.get('title', 'Unknown Title'),
            'duration': song_audio_info.get('duration'), 'thumbnail': song_audio_info.get('thumbnail'),
            'uploader': song_audio_info.get('uploader', 'Unknown Uploader'), 'requester': temp_requester,
            'stream_url': song_audio_info.get('url')})
        added_count += 1
    
    await client.save_guild_settings_to_file(guild_id)
    desc = f"Successfully added {added_count} songs to the queue." if mode == "append" else f"Successfully replaced the queue with {added_count} songs."
    if failed_count > 0: desc += f" ({failed_count} URLs failed to process or were skipped)."
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Queue Imported", desc), ephemeral_preference=False)

    if added_count > 0 and not vc.is_playing() and not client._current_song.get(guild_id) and client._queues[guild_id]:
        await client._play_guild_queue(guild_id)

async def _handle_settings_volume_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], level: int):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild: # Check Member and perms
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change the default volume."), ephemeral_preference=True); return
    
    guild_id = ctx_or_interaction.guild.id
    client.set_guild_volume(guild_id, level / 100.0)
    await client.save_guild_settings_to_file(guild_id)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Volume Set & Saved", f"Default music volume for this server is now **{level}%**. This has been applied to the current playback if active."), ephemeral_preference=True)


async def _handle_settings_loop_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], mode_value: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change the loop mode."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    client.set_guild_loop_mode(guild_id, mode_value)
    await client.save_guild_settings_to_file(guild_id)
    mode_name = {"off": "Off", "song": "Current Song", "queue": "Entire Queue"}.get(mode_value, mode_value.capitalize())
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Loop Mode Set & Saved", f"Default loop mode for this server is now: **{mode_name}**. This will apply to the current session."), ephemeral_preference=True)
    if mode_value == "off" and not client.get_guild_24_7_mode(guild_id):
        vc = client._voice_clients.get(guild_id)
        if vc and vc.is_connected() and not vc.is_playing() and not client._queues.get(guild_id) and not client._current_song.get(guild_id):
            await client.schedule_leave(guild_id)


async def _handle_settings_autoplay_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], status_bool: bool):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change autoplay settings."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    client.set_guild_smart_autoplay(guild_id, status_bool)
    await client.save_guild_settings_to_file(guild_id)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Smart Autoplay Set & Saved", f"Default smart autoplay for this server is now **{'ON' if status_bool else 'OFF'}**."), ephemeral_preference=True)


async def _handle_settings_247_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], status_bool: bool):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change 24/7 mode."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    client.set_guild_24_7_mode(guild_id, status_bool)
    # await client.save_guild_settings_to_file(guild_id) # Save is handled below after logic

    msg = f"24/7 Mode for this server is now **{'ON' if status_bool else 'OFF'}**."
    if status_bool:
        msg += " I will attempt to stay in the voice channel. Consider setting an autoplay genre for continuous music if the queue ends."
        vc = client._voice_clients.get(guild_id)
        if vc and vc.is_connected() and not vc.is_playing() and not client._queues.get(guild_id) and client.get_guild_autoplay_genre(guild_id):
            await client._play_guild_queue(guild_id) # Try to start genre autoplay
        # Cancel any pending leave task if 24/7 is turned ON
        if guild_id in client._leave_tasks: client._leave_tasks[guild_id].cancel(); client._leave_tasks.pop(guild_id, None)

    else: # Turning OFF
        client.set_last_known_vc_channel_id(guild_id, None) # Clear last known VC if 24/7 turned off
        vc = client._voice_clients.get(guild_id)
        if vc and vc.is_connected() and not vc.is_playing() and not client._queues.get(guild_id) and not client._current_song.get(guild_id):
            await client.schedule_leave(guild_id)
            msg += " Inactivity auto-leave is now active."
        else:
             msg += " If I'm idle, I will leave after a period of inactivity."
    
    await client.save_guild_settings_to_file(guild_id) # Save all changes
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("24/7 Mode Updated", msg), ephemeral_preference=True)


async def _handle_settings_autoplaygenre_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], genre: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change the autoplay genre."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    
    genre_to_set = genre.strip().lower()
    if genre_to_set == "clear" or not genre_to_set:
        client.set_guild_autoplay_genre(guild_id, None)
        msg = "24/7 Autoplay genre has been cleared. If 24/7 mode is on and the queue ends, I will use smart autoplay (if enabled) or remain silent."
    else:
        client.set_guild_autoplay_genre(guild_id, genre_to_set)
        msg = f"24/7 Autoplay genre for this server has been set to: **{genre_to_set.capitalize()}**."
        if client.get_guild_24_7_mode(guild_id):
            vc = client._voice_clients.get(guild_id)
            if vc and vc.is_connected() and not vc.is_playing() and not client._queues.get(guild_id):
                await client._play_guild_queue(guild_id) # Attempt to start new genre if idle
                msg += " Trying to start autoplay with the new genre now."

    await client.save_guild_settings_to_file(guild_id)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Autoplay Genre Updated", msg), ephemeral_preference=True)


async def _handle_settings_djrole_logic(
    ctx_or_interaction: Union[commands.Context, discord.Interaction],
    role_input_representation: Union[discord.Role, str] # Parameter can be a Role object or a string
):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.administrator:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Administrator' permission to set the DJ role."), ephemeral_preference=True); return
    
    guild = ctx_or_interaction.guild
    if not guild: # Should not happen with guild-based commands
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("This command must be used within a server."), ephemeral_preference=True); return
    guild_id = guild.id
    
    actual_role_to_set: Optional[discord.Role] = None
    clear_role_flag = False

    if isinstance(role_input_representation, str):
        # Input is a string (from slash command, or text command if RoleConverter failed)
        role_string_cleaned = role_input_representation.strip()
        if role_string_cleaned.lower() == 'clear':
            clear_role_flag = True
        else:
            # Attempt to find the role from the string
            # 1. Try by ID
            try:
                role_id_int = int(role_string_cleaned)
                found_role = guild.get_role(role_id_int)
            except ValueError: # Not an integer ID
                found_role = None

            # 2. Try by mention (if not found by ID)
            if not found_role:
                mention_match = re.match(r"<@&(\d+)>$", role_string_cleaned)
                if mention_match:
                    found_role = guild.get_role(int(mention_match.group(1)))
            
            # 3. Try by exact name (if not found by ID or mention)
            if not found_role:
                found_role = discord.utils.get(guild.roles, name=role_string_cleaned) # Case-sensitive

            # 4. Try by case-insensitive name (if still not found)
            if not found_role:
                for r_iter in guild.roles:
                    if r_iter.name.lower() == role_string_cleaned.lower():
                        found_role = r_iter
                        break
            
            if found_role:
                actual_role_to_set = found_role
            else:
                await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Role '{role_string_cleaned}' not found. Please provide a valid role name, ID, mention, or 'clear'."), ephemeral_preference=True); return

    elif isinstance(role_input_representation, discord.Role):
        # Input is already a Role object (likely from text command's RoleConverter)
        actual_role_to_set = role_input_representation

    # Proceed with the determined action
    if clear_role_flag:
        client.set_guild_dj_role_id(guild_id, None)
        await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("DJ Role Cleared", "The DJ role for this server has been cleared."), ephemeral_preference=True)
    elif actual_role_to_set:
        client.set_guild_dj_role_id(guild_id, actual_role_to_set.id)
        await client.save_guild_settings_to_file(guild_id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("DJ Role Set", f"The DJ role for this server has been set to **{actual_role_to_set.name}**. Users with this role will have controller permissions."), ephemeral_preference=True)
    else:
        # This state should ideally not be reached if logic above is correct
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Invalid input for DJ role. Please provide a role name, ID, mention, or 'clear'."), ephemeral_preference=True)

async def _handle_settings_view_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    guild_id = ctx_or_interaction.guild.id
    # Ensure settings are loaded (should be by on_guild_join or startup, but as a safeguard)
    if guild_id not in client._guild_settings: await client.load_guild_settings_from_file(guild_id)
    
    embed = discord.Embed(title=f"Saved Music Settings for {ctx_or_interaction.guild.name}", color=discord.Color.orange())
    embed.add_field(name="Volume", value=f"{int(client.get_guild_volume(guild_id)*100)}%").add_field(name="Loop Mode", value=client.get_guild_loop_mode(guild_id).capitalize())
    embed.add_field(name="Smart Autoplay", value="✅ On" if client.get_guild_smart_autoplay(guild_id) else "❌ Off")
    embed.add_field(name="24/7 Mode", value="✅ On" if client.get_guild_24_7_mode(guild_id) else "❌ Off")
    autoplay_genre = client.get_guild_autoplay_genre(guild_id)
    embed.add_field(name="24/7 Autoplay Genre", value=autoplay_genre.capitalize() if autoplay_genre else "Not Set")
    
    dj_role_id = client.get_guild_dj_role_id(guild_id)
    dj_role_name = "Not Set"
    if dj_role_id:
        role = ctx_or_interaction.guild.get_role(dj_role_id)
        dj_role_name = role.name if role else f"ID: {dj_role_id} (Role not found)"
    embed.add_field(name="DJ Role", value=dj_role_name)
    
    embed.add_field(name="Audio Effects", value=client.get_active_effects_display(guild_id), inline=False)
    embed.set_footer(text="These are the currently saved default settings for this server.")
    await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=True)


async def _apply_effect_and_restart(guild_id: int, interaction_or_ctx: Union[discord.Interaction, commands.Context]):
    vc = client._voice_clients.get(guild_id); current_song = client._current_song.get(guild_id)
    if vc and (vc.is_playing() or vc.is_paused()) and current_song and not current_song.get('is_live_stream'):
        # For interactions, the initial response is already sent by the handler.
        # This is an additional notification.
        if isinstance(interaction_or_ctx, discord.Interaction):
             # Followup if main response done, otherwise edit/send to channel if possible.
            try:
                if interaction_or_ctx.response.is_done():
                    await interaction_or_ctx.followup.send("Attempting to restart song with new effect(s)...", ephemeral=True)
                # Else: main response from handler covers it. This message is just extra.
            except discord.HTTPException: pass # Best effort
        else: # Text command
            await interaction_or_ctx.channel.send("Attempting to restart song with new effect(s)...")

        accumulated_time = current_song.get('accumulated_play_time_seconds', 0.0)
        if current_song.get('play_start_utc'): accumulated_time += (datetime.datetime.now(timezone.utc) - current_song['play_start_utc']).total_seconds()
        
        song_duration = current_song.get('duration')
        # Ensure seek time is valid
        if isinstance(song_duration, (int,float)) and accumulated_time >= song_duration :
             accumulated_time = song_duration - 0.1 if song_duration > 0.1 else 0.0
        
        song_to_replay = current_song.copy()
        # vc.stop() is handled by _play_guild_queue now
        await client._play_guild_queue(guild_id, song_to_replay=song_to_replay, seek_seconds=max(0, accumulated_time))
    elif current_song and current_song.get('is_live_stream'):
        msg = "Effect saved. Live streams cannot be restarted; effect will apply to the next non-live song or if the stream reconnects."
        if isinstance(interaction_or_ctx, discord.Interaction):
            if interaction_or_ctx.response.is_done(): await interaction_or_ctx.followup.send(msg, ephemeral=True)
        else: await interaction_or_ctx.channel.send(msg)


async def _handle_effects_apply_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], effect_value: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to change audio effects."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    
    # Defer for interactions as applying effect might involve restarting song
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=True)

    filter_parts = []
    # Base sample rate for asetrate calculations if needed, assuming 48kHz output
    samplerate = "48000" 

    if effect_value == "bass_low": filter_parts.append("bass=g=3")
    elif effect_value == "bass_medium": filter_parts.append("bass=g=6")
    elif effect_value == "bass_high": filter_parts.append("bass=g=9") # Higher bass boost
    elif effect_value == "vocal_boost": filter_parts.append("equalizer=f=1500:width_type=h:width=1000:g=3,equalizer=f=2500:width_type=h:width=1000:g=2") # Simple EQ boost for mid-range vocals
    elif effect_value == "treble_boost": filter_parts.append("treble=g=5")
    elif effect_value == "nightcore": filter_parts.extend([f"asetrate={samplerate}*1.25", "atempo=1.20"]) # Speed up pitch and tempo
    elif effect_value == "vaporwave": filter_parts.extend([f"asetrate={samplerate}*0.8", "atempo=0.8", "aecho=0.8:0.9:500:0.3"]) # Slow down, pitch down, echo
    elif effect_value == "karaoke": filter_parts.append("stereotools=mlev=0.015") # Attempt vocal reduction (hit or miss)
    elif effect_value == "pitch_up": filter_parts.extend([f"asetrate={samplerate}*1.05946", "atempo=0.94387"]) # +1 semitone, duration preserved
    elif effect_value == "pitch_down": filter_parts.extend([f"asetrate={samplerate}*0.94387", "atempo=1.05946"]) # -1 semitone, duration preserved
    elif effect_value == "slowed_tempo": filter_parts.append("atempo=0.85") # Tempo only
    elif effect_value == "spedup_tempo": filter_parts.append("atempo=1.15") # Tempo only
    elif effect_value == "reverb_small": filter_parts.append("aecho=0.8:0.9:40:0.3") # Small room echo
    elif effect_value == "reverb_large": filter_parts.append("aecho=0.8:0.9:1000:0.3") # Large hall echo

    # Determine final filter string
    if effect_value == "clear": final_filter_string = DEFAULT_AUDIO_FILTERS
    elif effect_value == "raw": final_filter_string = "" # No filters at all
    else:
        # Add default loudness normalization if the chosen effect isn't fundamentally altering loudness already
        # and doesn't include its own loudnorm.
        is_loudness_altering = any(keyword in effect_value for keyword in ["bass", "vocal", "treble", "karaoke"])
        has_loudnorm = any("loudnorm" in fp for fp in filter_parts)
        
        if filter_parts and not is_loudness_altering and not has_loudnorm:
            filter_parts.append(LOUDNESS_NORMALIZATION_FILTER)
        
        final_filter_string = ",".join(filter(None, filter_parts)).strip(',')
        if not final_filter_string and effect_value not in ["raw", "clear"]: # Fallback if parts somehow resulted in empty
            final_filter_string = DEFAULT_AUDIO_FILTERS


    client.set_guild_ffmpeg_filters(guild_id, final_filter_string)
    await client.save_guild_settings_to_file(guild_id)
    
    effect_name_display = next((c.name for c in EFFECT_CHOICES if c.value == effect_value), effect_value.replace("_", " ").capitalize())
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Audio Effect Set & Saved", f"Default audio effect for this server set to: **{effect_name_display}**. Applied (restarting current song if applicable)."), ephemeral_preference=True)
    await _apply_effect_and_restart(guild_id, ctx_or_interaction)


async def _handle_effects_custom_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], filter_string: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    if not isinstance(user_obj, discord.Member) or not user_obj.guild_permissions.manage_guild:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You need 'Manage Server' permission to set custom audio effects."), ephemeral_preference=True); return
    guild_id = ctx_or_interaction.guild.id
    
    if isinstance(ctx_or_interaction, discord.Interaction) and not ctx_or_interaction.response.is_done():
        await ctx_or_interaction.response.defer(ephemeral=True)

    processed_filter = filter_string.strip(); display_name = "Custom Filters"
    
    if processed_filter.lower() == "clear":
        client.set_guild_ffmpeg_filters(guild_id, DEFAULT_AUDIO_FILTERS); display_name = "Default (Loudness Normalization)"
    elif processed_filter.lower() == "raw":
        client.set_guild_ffmpeg_filters(guild_id, ""); display_name = "Raw (No Effects)"
    else:
        client.set_guild_ffmpeg_filters(guild_id, processed_filter)
    
    await client.save_guild_settings_to_file(guild_id)
    current_val = client.get_guild_ffmpeg_filters(guild_id)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Custom Audio Effect Set & Saved", f"Custom FFmpeg filter string set to: `{current_val if current_val else 'None'}` (interpreted as **{display_name}**). Applied (restarting current song if applicable)."), ephemeral_preference=True)
    await _apply_effect_and_restart(guild_id, ctx_or_interaction)


async def _handle_controller_transfer_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], member: discord.Member):
    guild_id = ctx_or_interaction.guild.id
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    
    # Check if invoker is Admin OR the original joiner
    is_admin = isinstance(user_obj, discord.Member) and user_obj.guild_permissions.administrator
    is_original_joiner = client._original_joiner.get(guild_id) == user_obj.id
    
    if not (is_admin or is_original_joiner):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only the original session starter or a server administrator can transfer primary control."), ephemeral_preference=True); return
    if member.bot:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Cannot transfer control to a bot."), ephemeral_preference=True); return
    if member.id == client._original_joiner.get(guild_id):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"{member.mention} is already the primary controller."), ephemeral_preference=True); return
    
    client._original_joiner[guild_id] = member.id
    client._session_controllers.setdefault(guild_id, []).clear() # New primary resets other explicit controllers
    client._session_controllers[guild_id].append(member.id) # Add new primary to controller list too
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Primary Control Transferred", f"Primary music control for this session has been transferred to {member.mention}."), ephemeral_preference=False)


async def _handle_controller_add_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], member: discord.Member):
    if not client.is_controller(ctx_or_interaction): # is_controller checks admin/original joiner/DJ role/explicitly added
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only current controllers or admins can add additional controllers."), ephemeral_preference=True); return
    if member.bot:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Cannot add a bot as a controller."), ephemeral_preference=True); return
    
    guild_id = ctx_or_interaction.guild.id
    client._session_controllers.setdefault(guild_id, [])
    
    # Ensure original joiner is implicitly always a controller, or explicitly if not already
    og_joiner_id = client._original_joiner.get(guild_id)
    if og_joiner_id and og_joiner_id not in client._session_controllers[guild_id]:
        client._session_controllers[guild_id].append(og_joiner_id)
        
    if member.id not in client._session_controllers[guild_id] and member.id != og_joiner_id: # Don't add if already primary or in list
        client._session_controllers[guild_id].append(member.id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Controller Added", f"{member.mention} can now use restricted music commands for this session."), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"{member.mention} is already a controller or the primary session starter."), ephemeral_preference=True)


async def _handle_controller_remove_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], member: discord.Member):
    guild_id = ctx_or_interaction.guild.id
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author

    is_admin = isinstance(user_obj, discord.Member) and user_obj.guild_permissions.administrator
    is_original_joiner = client._original_joiner.get(guild_id) == user_obj.id

    if not (is_admin or is_original_joiner):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Only the original session starter or a server administrator can remove controllers."), ephemeral_preference=True); return
    if member.id == client._original_joiner.get(guild_id):
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Cannot remove the primary session controller ({member.mention}). Transfer control first if needed."), ephemeral_preference=True); return
    
    if guild_id in client._session_controllers and member.id in client._session_controllers[guild_id]:
        client._session_controllers[guild_id].remove(member.id)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Controller Removed", f"{member.mention} is no longer an additional session controller."), ephemeral_preference=False)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"{member.mention} was not found in the list of additional controllers."), ephemeral_preference=True)


async def _handle_controller_list_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    guild_id = ctx_or_interaction.guild.id
    ctrl_list_ids = client._session_controllers.get(guild_id, [])
    og_joiner_id = client._original_joiner.get(guild_id)
    
    if not og_joiner_id and not ctrl_list_ids :
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("No active music session or no controllers defined."), ephemeral_preference=True); return
    
    embed = discord.Embed(title="🎧 Music Session Controllers", color=discord.Color.info())
    primary_mention = "Not set (session might not be active or started by bot itself)."
    if og_joiner_id:
        og_member = ctx_or_interaction.guild.get_member(og_joiner_id)
        primary_mention = og_member.mention if og_member else f"User ID: {og_joiner_id} (Member not found in server?)"
    
    add_mentions = []
    for uid in ctrl_list_ids:
        if uid != og_joiner_id: # Don't list primary again if they are in explicit list
            member = ctx_or_interaction.guild.get_member(uid)
            add_mentions.append(member.mention if member else f"User ID: {uid} (Left?)")
            
    dj_role_id = client.get_guild_dj_role_id(guild_id)
    dj_role_info = "Not set"
    if dj_role_id:
        dj_role = ctx_or_interaction.guild.get_role(dj_role_id)
        dj_role_info = dj_role.mention if dj_role else f"ID: {dj_role_id} (Role deleted?)"

    embed.add_field(name="👑 Primary Controller (Session Starter)", value=primary_mention, inline=False)
    embed.add_field(name="🎧 DJ Role (Server Setting)", value=dj_role_info, inline=False)
    embed.add_field(name="🕹️ Additional Session Controllers", value=", ".join(add_mentions) if add_mentions else "None", inline=False)
    embed.set_footer(text="Admins always have controller permissions.")
    await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=True)


async def _handle_playlist_save_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], name: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    guild_id = ctx_or_interaction.guild.id
    
    full_q = []
    if client._current_song.get(guild_id): full_q.append(client._current_song[guild_id].copy())
    full_q.extend(s.copy() for s in client._queues.get(guild_id,[]))
    if not full_q:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("The queue is empty. Nothing to save."), ephemeral_preference=True); return

    name_norm = name.strip().lower() # Normalize name for storage key
    if not (1 <= len(name.strip()) <= 50): # Use original name for length check display
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("Playlist name must be between 1 and 50 characters."), ephemeral_preference=True); return
    
    user_pls = load_user_playlists(user_obj.id)
    if len(user_pls) >= 20 and name_norm not in user_pls: # Max 20 playlists, unless overwriting
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You have reached the maximum of 20 saved playlists. Delete an old one to save a new one."), ephemeral_preference=True); return
    
    # Save only essential, non-dynamic info
    pl_to_save = [{'title': s.get('title'), 'webpage_url': s.get('webpage_url'),
                   'duration': s.get('duration'), 'thumbnail': s.get('thumbnail'),
                   'uploader': s.get('uploader')} for s in full_q if s.get('webpage_url')]
    if not pl_to_save:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("No songs with valid URLs in the queue to save."), ephemeral_preference=True); return

    user_pls[name_norm] = pl_to_save; save_user_playlists(user_obj.id, user_pls)
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Playlist Saved", f"Playlist '**{name.strip()}**' with {len(pl_to_save)} songs has been saved!"), ephemeral_preference=True)


async def _handle_playlist_load_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], name: str, mode_value: str):
    is_interaction = isinstance(ctx_or_interaction, discord.Interaction)
    if is_interaction:
        if not ctx_or_interaction.response.is_done(): await ctx_or_interaction.response.defer(thinking=True)
    else: await ctx_or_interaction.typing()
    
    guild_id = ctx_or_interaction.guild.id
    user_obj = ctx_or_interaction.user if is_interaction else ctx_or_interaction.author

    vc = await client.ensure_voice_client(ctx_or_interaction, join_if_not_connected=True)
    if not vc: return # Error handled by ensure_voice_client

    user_pls = load_user_playlists(user_obj.id); name_norm = name.strip().lower()
    pl_to_load_refs = user_pls.get(name_norm)
    if not pl_to_load_refs:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Playlist '**{name.strip()}**' not found in your saved playlists."), ephemeral_preference=True); return

    client._queues.setdefault(guild_id, [])
    if mode_value == "replace":
        client._queues[guild_id] = [] # Clear current server queue
        if client._current_song.get(guild_id): # If a song is playing, stop it
            if vc.is_playing() or vc.is_paused(): vc.stop()
            client._current_song[guild_id] = None # Clear current song
    
    added_count = 0; failed_count = 0
    initial_queue_size = len(client._queues[guild_id])

    for song_ref in pl_to_load_refs:
        if initial_queue_size + added_count >= MAX_QUEUE_SIZE:
            await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Queue is full. Successfully added {added_count} songs. {failed_count} URLs failed or were skipped."), ephemeral_preference=True); break
        if not isinstance(song_ref, dict) or not song_ref.get('webpage_url'):
            failed_count +=1; continue
        
        # Fetch fresh audio info for stream URL and up-to-date metadata
        audio_info = await get_audio_stream_info(song_ref['webpage_url'])
        if not audio_info or "error" in audio_info or not audio_info.get('url'):
            failed_count += 1; continue

        client._queues[guild_id].append({
            'webpage_url': audio_info.get('webpage_url'), 
            'title': audio_info.get('title', song_ref.get('title', 'Unknown Title')), # Prefer fresh title
            'duration': audio_info.get('duration', song_ref.get('duration')),
            'thumbnail': audio_info.get('thumbnail', song_ref.get('thumbnail')),
            'uploader': audio_info.get('uploader', song_ref.get('uploader')),
            'requester': user_obj.mention, # Playlist loader is the requester
            'stream_url': audio_info.get('url') # Crucial: fresh stream URL
        }); added_count += 1
    
    await client.save_guild_settings_to_file(guild_id)
    desc = f"Successfully added {added_count} songs from playlist '**{name.strip()}**' to the queue." if mode_value == "append" else f"Successfully replaced the queue with {added_count} songs from playlist '**{name.strip()}**'."
    if failed_count > 0: desc += f" ({failed_count} songs from the playlist failed to load)."
    await send_custom_response(ctx_or_interaction, embed=create_success_embed("Playlist Loaded", desc), ephemeral_preference=False)

    if added_count > 0 and not vc.is_playing() and not client._current_song.get(guild_id) and client._queues.get(guild_id):
        await client._play_guild_queue(guild_id)


async def _handle_playlist_list_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction]):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    user_pls = load_user_playlists(user_obj.id)
    if not user_pls:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed("You have no saved playlists."), ephemeral_preference=True); return
    
    embed = discord.Embed(title=f"📋 {user_obj.display_name}'s Saved Playlists", color=discord.Color.gold())
    pl_strs = [f"• **{pl_name.capitalize()}** ({len(s_list)} song{'s' if len(s_list)!=1 else ''})" 
               for i, (pl_name, s_list) in enumerate(user_pls.items()) if i<25] # Display up to 25
    if len(user_pls) > 25 : pl_strs.append(f"... and {len(user_pls)-25} more.")
    embed.description = "\n".join(pl_strs) if pl_strs else "No playlists found." # Should be caught by earlier check
    embed.set_footer(text=f"You have {len(user_pls)} saved playlist(s). Max: 20.") # Note: Max is 20, but we display 25 if more somehow exist
    await send_custom_response(ctx_or_interaction, embed=embed, ephemeral_preference=True)


async def _handle_playlist_delete_logic(ctx_or_interaction: Union[commands.Context, discord.Interaction], name: str):
    user_obj = ctx_or_interaction.user if isinstance(ctx_or_interaction, discord.Interaction) else ctx_or_interaction.author
    user_pls = load_user_playlists(user_obj.id); name_norm = name.strip().lower()
    if name_norm in user_pls:
        del user_pls[name_norm]; save_user_playlists(user_obj.id, user_pls)
        await send_custom_response(ctx_or_interaction, embed=create_success_embed("Playlist Deleted", f"Playlist '**{name.strip()}**' has been deleted from your saved playlists."), ephemeral_preference=True)
    else:
        await send_custom_response(ctx_or_interaction, embed=create_error_embed(f"Playlist '**{name.strip()}**' not found in your saved playlists."), ephemeral_preference=True)


# --- TEXT COMMANDS (using shared handlers) ---
@client.command(name="play", aliases=['p'], help="Plays song. `play <URL or search>`")
@commands.cooldown(1, 3.0, type=commands.BucketType.user)
async def text_play(ctx: commands.Context, *, query: Optional[str] = None):
    if not query: await send_custom_response(ctx, content=f"Please provide a song URL or search term. Usage: `{ctx.prefix}play <URL or search term>`", ephemeral_preference=False); return
    if not ctx.author.voice or not ctx.author.voice.channel:
        await send_custom_response(ctx, embed=create_error_embed("You need to be in a voice channel to use this command."), ephemeral_preference=False); return
    await _handle_play_logic(ctx.bot, ctx, query) # Pass ctx.bot as the first argument

@client.command(name="skip", aliases=['s'], help="Skips current song.")
@commands.cooldown(1, 2.0, type=commands.BucketType.user)
async def text_skip(ctx: commands.Context): await _handle_skip_logic(ctx)

@client.command(name="stop", help="Stops playback, clears queue, leaves.")
@commands.cooldown(1, 5.0, type=commands.BucketType.guild)
async def text_stop(ctx: commands.Context): await _handle_stop_logic(ctx)

@client.command(name="nowplaying", aliases=['np'], help="Shows current song.")
async def text_nowplaying(ctx: commands.Context): await _handle_nowplaying_logic(ctx)

@client.command(name="lyrics", aliases=['ly'], help="Shows lyrics. `lyrics [song title]`")
@commands.cooldown(1, 10.0, type=commands.BucketType.user)
async def text_lyrics(ctx: commands.Context, *, song_title_query: Optional[str] = None): await _handle_lyrics_logic(ctx, song_title_query)

@client.command(name="queue", aliases=['q', 'viewqueue'], help="Shows queue. `queue [page_number]`")
async def text_queue(ctx: commands.Context, page_str: Optional[str] = "1"):
    # The _display_queue_view_logic will create a QueueView starting at page 0 by default
    # For text command, if you want to respect the page number, you'd adjust how QueueView is instantiated.
    # However, the QueueView itself handles pagination.
    # So, for the text command, we can just call the logic.
    # The page_str argument is less relevant if QueueView starts at page 0 and handles internal paging.

    # We'll call _display_queue_view_logic which will instantiate QueueView at its default start page.
    await _display_queue_view_logic(ctx)


@client.command(name="clearqueue", aliases=["clearq"], help="Clears queue.")
async def text_clearqueue(ctx: commands.Context): await _handle_queue_clear_logic(ctx)

@client.command(name="remove", aliases=["rem"], help="Removes song. `remove <idx or title part>`")
async def text_remove(ctx: commands.Context, *, identifier: str): await _handle_queue_remove_logic(ctx, identifier)

@client.command(name="removerange", help="Removes range. `removerange <start_idx> <end_idx>`")
async def text_removerange(ctx: commands.Context, start_index: int, end_index: int): await _handle_queue_removerange_logic(ctx, start_index, end_index)

@client.command(name="shuffle", help="Shuffles queue.")
async def text_shuffle(ctx: commands.Context): await _handle_queue_shuffle_logic(ctx)

@client.command(name="move", aliases=["mv"], help="Moves song. `move <from_idx> <to_idx>`")
async def text_move(ctx: commands.Context, from_index: int, to_index: int): await _handle_queue_move_logic(ctx, from_index, to_index)

@client.command(name="jump", help="Jumps to song. `jump <idx or title part>`")
async def text_jump(ctx: commands.Context, *, identifier: str): await _handle_queue_jump_logic(ctx, identifier)

@client.command(name="importqueue", aliases=["iq"], help="Import queue from URL. `iq <url> [append|replace]`")
async def text_importqueue(ctx: commands.Context, url: str, mode: str = "append"):
    if mode.lower() not in ["append", "replace"]:
        await send_custom_response(ctx, content="Invalid mode. Please use 'append' or 'replace'.", ephemeral_preference=False); return
    await _handle_queue_import_logic(ctx, url, mode.lower())

@client.command(name="volume", aliases=['vol'], help="Sets default volume (0-200), saved. `volume <level>`")
async def text_volume(ctx: commands.Context, level_str: Optional[str] = None):
    if level_str is None:
        await send_custom_response(ctx, content=f"🔊 Current default volume: {int(client.get_guild_volume(ctx.guild.id)*100)}%. Use `{ctx.prefix}volume <0-200>` to set.", ephemeral_preference=False); return
    try:
        level = int(level_str)
        if not (0 <= level <= 200): raise ValueError("Volume out of range")
    except ValueError:
        await send_custom_response(ctx, embed=create_error_embed("Invalid volume level. Please provide a number between 0 and 200."), ephemeral_preference=False); return
    await _handle_settings_volume_logic(ctx, level)

@client.command(name="loop", help="Sets default loop mode, saved. `loop <off|song|queue>`")
async def text_loop(ctx: commands.Context, mode: Optional[str] = None):
    valid_modes = {"off": "Off", "song": "Song", "queue": "Queue"}
    current_mode_val = client.get_guild_loop_mode(ctx.guild.id)
    current_mode_display = valid_modes.get(current_mode_val, "Unknown")
    if mode is None:
        await send_custom_response(ctx, content=f"🔁 Current loop mode: **{current_mode_display}**. Use `{ctx.prefix}loop <off|song|queue>` to set.", ephemeral_preference=False); return
    if mode.lower() not in valid_modes:
        await send_custom_response(ctx, embed=create_error_embed("Invalid loop mode. Please use `off`, `song`, or `queue`."), ephemeral_preference=False); return
    await _handle_settings_loop_logic(ctx, mode.lower())

@client.command(name="autoplay", help="Toggles default smart autoplay, saved. `autoplay <on|off>`")
async def text_autoplay(ctx: commands.Context, status: Optional[str] = None):
    current_status = client.get_guild_smart_autoplay(ctx.guild.id)
    if status is None:
        await send_custom_response(ctx, content=f"🤖 Current smart autoplay status: **{'ON' if current_status else 'OFF'}**. Use `{ctx.prefix}autoplay <on|off>` to set.", ephemeral_preference=False); return
    if status.lower() not in ["on", "off"]:
        await send_custom_response(ctx, embed=create_error_embed("Invalid status. Please use `on` or `off`."), ephemeral_preference=False); return
    await _handle_settings_autoplay_logic(ctx, status.lower() == "on")

@client.command(name="247", aliases=["24seven"], help="Toggles 24/7 mode, saved. `247 <on|off>`")
async def text_247(ctx: commands.Context, status: Optional[str] = None):
    current_status = client.get_guild_24_7_mode(ctx.guild.id)
    if status is None:
        await send_custom_response(ctx, content=f"🕒 Current 24/7 mode status: **{'ON' if current_status else 'OFF'}**. Use `{ctx.prefix}247 <on|off>` to set.", ephemeral_preference=False); return
    if status.lower() not in ["on", "off"]:
        await send_custom_response(ctx, embed=create_error_embed("Invalid status. Please use `on` or `off`."), ephemeral_preference=False); return
    await _handle_settings_247_logic(ctx, status.lower() == "on")

@client.command(name="autoplaygenre", help="Sets 24/7 autoplay genre, saved. `autoplaygenre <genre|clear>`")
async def text_autoplaygenre(ctx: commands.Context, *, genre: Optional[str] = None):
    current_genre = client.get_guild_autoplay_genre(ctx.guild.id)
    if genre is None:
        await send_custom_response(ctx, content=f"🎶 Current 24/7 autoplay genre: **{current_genre.capitalize() if current_genre else 'Not Set'}**. Use `{ctx.prefix}autoplaygenre <genre name | clear>` to set.", ephemeral_preference=False); return
    await _handle_settings_autoplaygenre_logic(ctx, genre)

@client.command(name="setdjrole", help="Sets or clears the DJ role (Admin only). `setdjrole <role name/ID | @role | clear>`")
@commands.has_permissions(administrator=True)
async def text_setdjrole(ctx: commands.Context, *, role_input_str: str):
    role_to_pass_to_logic: Union[discord.Role, str] # This will be passed to _handle_settings_djrole_logic

    cleaned_input = role_input_str.strip()
    if cleaned_input.lower() == 'clear':
        role_to_pass_to_logic = 'clear'
    else:
        try:
            # RoleConverter handles mentions, IDs, and names well for text commands
            role_to_pass_to_logic = await commands.RoleConverter().convert(ctx, cleaned_input)
        except commands.RoleNotFound:
            # If RoleConverter fails, your on_command_error will catch RoleNotFound.
            # Alternatively, to let _handle_settings_djrole_logic try a more basic string match:
            # role_to_pass_to_logic = cleaned_input 
            # But then you'd want to remove the RoleNotFound from being a major error in on_command_error for this cmd.
            # For now, let RoleConverter's failure be the error for text commands.
            await send_custom_response(ctx, embed=create_error_embed(f"Role '{cleaned_input}' not found. Please provide a valid role name, ID, mention, or 'clear'."), ephemeral_preference=False); return
    
    await _handle_settings_djrole_logic(ctx, role_to_pass_to_logic)

@client.command(name="settings", aliases=["viewsettings"], help="View saved music settings for this server.")
async def text_settings(ctx: commands.Context): await _handle_settings_view_logic(ctx)

@client.command(name="effect", aliases=["effects", "filter"], help="Apply effect, saved. `effect <name|custom> [custom_filter_string]`")
async def text_effect(ctx: commands.Context, effect_name_or_custom: str, *, filter_str_custom: Optional[str] = None):
    if effect_name_or_custom.lower() == "custom":
        if not filter_str_custom:
            await send_custom_response(ctx, content=f"Usage: `{ctx.prefix}effect custom <ffmpeg_filter_string>` or `{ctx.prefix}effect custom clear/raw`", ephemeral_preference=False); return
        await _handle_effects_custom_logic(ctx, filter_str_custom); return
    
    val_to_apply = next((c.value for c in EFFECT_CHOICES if c.name.lower() == effect_name_or_custom.lower() or c.value.lower() == effect_name_or_custom.lower()), None)
    if val_to_apply is None:
        names = ", ".join([f"`{c.name}` (`{c.value}`)" for c in EFFECT_CHOICES])
        await send_custom_response(ctx, embed=create_error_embed(f"Invalid effect name or value. Choose from: {names}\nOr use `{ctx.prefix}effect custom ...`"), ephemeral_preference=False); return
    await _handle_effects_apply_logic(ctx, val_to_apply)

@client.command(name="transfercontroller", aliases=["tc", "transferdj"], help="Transfer primary control. `tc @user`")
async def text_transfercontroller(ctx: commands.Context, member: discord.Member): await _handle_controller_transfer_logic(ctx, member)

@client.command(name="addcontroller", aliases=["adddj"], help="Add session controller. `adddj @user`")
async def text_addcontroller(ctx: commands.Context, member: discord.Member): await _handle_controller_add_logic(ctx, member)

@client.command(name="removecontroller", aliases=["remdj", "removedj"], help="Remove session controller. `remdj @user`")
async def text_removecontroller(ctx: commands.Context, member: discord.Member): await _handle_controller_remove_logic(ctx, member)

@client.command(name="listcontrollers", aliases=["djlist", "controllers"], help="List session controllers.")
async def text_listcontrollers(ctx: commands.Context): await _handle_controller_list_logic(ctx)

@client.command(name="playlistsave", aliases=["psave"], help="Save current queue to a playlist. `psave <playlist_name>`")
async def text_playlistsave(ctx: commands.Context, *, name: str): await _handle_playlist_save_logic(ctx, name)

@client.command(name="playlistload", aliases=["pload"], help="Load a playlist. `pload <playlist_name> [append|replace]`")
async def text_playlistload(ctx: commands.Context, name: str, mode: str = "append"):
    if mode.lower() not in ["append", "replace"]:
        await send_custom_response(ctx, content="Invalid mode. Please use 'append' or 'replace'.", ephemeral_preference=False); return
    await _handle_playlist_load_logic(ctx, name, mode.lower())

@client.command(name="playlist", aliases=["pl", "playlists"], help="List your saved playlists.")
async def text_playlist(ctx: commands.Context): await _handle_playlist_list_logic(ctx)

@client.command(name="playlistdelete", aliases=["pdel", "playlistremove"], help="Delete a playlist. `pdel <playlist_name>`")
async def text_playlistdelete(ctx: commands.Context, *, name: str): await _handle_playlist_delete_logic(ctx, name)


# --- Error Handler for Text Commands ---
@client.event
async def on_command_error(ctx: commands.Context, error: commands.CommandError):
    if isinstance(error, commands.CommandNotFound): return # Ignore unknown commands
    
    error_message_str = "An error occurred with that command."
    ephemeral_pref = False # Text command errors are public

    if isinstance(error, commands.MissingRequiredArgument):
        error_message_str = f"You're missing a required argument: `{error.param.name}`.\nCorrect usage: `{ctx.prefix}{ctx.command.qualified_name} {ctx.command.signature}`"
    elif isinstance(error, (commands.BadArgument, commands.UserInputError)):
        error_message_str = f"Invalid input provided for `{ctx.command.qualified_name}`.\nCorrect usage: `{ctx.prefix}{ctx.command.qualified_name} {ctx.command.signature}`"
    elif isinstance(error, commands.CommandOnCooldown):
        error_message_str = f"The command `{ctx.command.qualified_name}` is on cooldown. Please try again in {error.retry_after:.2f} seconds."
    elif isinstance(error, commands.MissingPermissions):
        error_message_str = f"You lack the necessary permissions to use `{ctx.command.qualified_name}`: {', '.join(error.missing_permissions)}."
    elif isinstance(error, commands.BotMissingPermissions):
        error_message_str = f"I lack the necessary permissions to perform `{ctx.command.qualified_name}`: {', '.join(error.missing_permissions)}."
    elif isinstance(error, commands.CheckFailure): # Generic check failure
        error_message_str = f"You do not meet the requirements to use the command `{ctx.command.qualified_name}`. This might be due to controller/DJ role restrictions or other checks."
    elif isinstance(error, commands.NoPrivateMessage):
        error_message_str = f"The command `{ctx.command.qualified_name}` cannot be used in private messages."
    elif isinstance(error, commands.CommandInvokeError):
        original = error.original
        print(f"Text command '{ctx.command.qualified_name}' raised an exception: {original}", file=sys.stderr)
        traceback.print_exception(type(original), original, original.__traceback__, file=sys.stderr)
        error_message_str = f"An internal error occurred while executing `{ctx.command.qualified_name}`: {truncate_text(str(original), 150)}"
    else:
        print(f'An unhandled text command error occurred for command {ctx.command.qualified_name if ctx.command else "UnknownCmd"}: {error}', file=sys.stderr)
        traceback.print_exception(type(error), error, error.__traceback__, file=sys.stderr)
        error_message_str = f"An unexpected error occurred with `{ctx.command.qualified_name if ctx.command else 'that command'}`."

    await send_custom_response(ctx, embed=create_error_embed(error_message_str), ephemeral_preference=ephemeral_pref)


# --- Event Handlers ---
@client.event
async def on_ready():
    print(f'Logged in as {client.user} (ID: {client.user.id})')
    print(f'Currently in {len(client.guilds)} guilds. Default prefix: {client.default_prefix_val}')
    print(f'Bot started: {client.start_time.strftime("%Y-%m-%d %H:%M:%S UTC")}')
    print('------')
    activity_name = f"music in {len(client.guilds)} servers! /help"
    try:
        await client.change_presence(activity=discord.Activity(type=discord.ActivityType.listening, name=activity_name))
    except Exception as e:
        print(f"Error setting presence: {e}")


# Global function or method of MyClient
async def _initiate_play_from_embed(
    client_instance: 'MyClient', # Pass client instance if global
    message: discord.Message, 
    derived_query: str
):
    print(f"\nDEBUG EMBED_INIT: Called with derived_query: '{derived_query}' for user {message.author.name} in guild {message.guild.name if message.guild else 'N/A'}")

    guild = message.guild
    if not guild: print("DEBUG EMBED_INIT: No guild. Cannot proceed."); return
    guild_id = guild.id
    user_obj = message.author
    text_channel = message.channel

    if not isinstance(user_obj, discord.Member) or not user_obj.voice or not user_obj.voice.channel:
        print(f"DEBUG EMBED_INIT: User {user_obj.name} not in VC."); return

    # ... (PseudoContext setup as before, using client_instance for ensure_voice_client)
    author_member = guild.get_member(user_obj.id)
    if not author_member: print(f"DEBUG EMBED_INIT: Could not get Member for {user_obj.id}."); return
    class PseudoContext:
        def __init__(self, msg_obj, author_as_member): self.guild=msg_obj.guild; self.user=author_as_member; self.author=author_as_member; self.channel=msg_obj.channel; self.response=None; self.followup=None; self.message=msg_obj
    pseudo_ctx = PseudoContext(message, author_member)
    vc = await client_instance.ensure_voice_client(pseudo_ctx, join_if_not_connected=True) # Use client_instance
    if not vc: print("DEBUG EMBED_INIT: ensure_voice_client failed."); return

    is_search_from_embed = derived_query.startswith("ytsearch:") or derived_query.startswith("scsearch:")
    actual_query_for_ytdl = derived_query
    search_provider_for_ytdl = "youtube" # Default
    if derived_query.startswith("scsearch:"):
        search_provider_for_ytdl = "soundcloud"
        actual_query_for_ytdl = derived_query[len("scsearch:"):]
    elif derived_query.startswith("ytsearch:"):
        search_provider_for_ytdl = "youtube"
        actual_query_for_ytdl = derived_query[len("ytsearch:"):]
    
    print(f"DEBUG EMBED_INIT: Calling get_audio_stream_info with query='{actual_query_for_ytdl}', search={is_search_from_embed}, provider='{search_provider_for_ytdl}'")
    song_audio_info = await get_audio_stream_info(
        actual_query_for_ytdl, # The clean search term or direct URL
        search=is_search_from_embed,
        search_results_count=1, # For embed auto-play, we take the top result
        search_provider=search_provider_for_ytdl
    )

    if not song_audio_info or "error" in song_audio_info or \
       not song_audio_info.get('title') or \
       not song_audio_info.get('webpage_url') or \
       not song_audio_info.get('url'): # 'url' here MUST be the stream_url
        
        err_msg = "Could not get essential track information (title, webpage, or stream URL)."
        title_err_context = derived_query
        if song_audio_info:
            if "error" in song_audio_info: err_msg = song_audio_info['error']
            if song_audio_info.get("title"): title_err_context = song_audio_info.get("title")
        
        print(f"DEBUG EMBED_INIT: Failed to add. Error: '{err_msg}', Context: '{title_err_context}', Info: {str(song_audio_info)[:200]}")
        try: await text_channel.send(embed=create_error_embed(f"Failed to play from link embed '{truncate_text(title_err_context,60)}': {err_msg}"))
        except discord.HTTPException: pass
        return

    # At this point, song_audio_info should be a valid dict with 'webpage_url' and 'url' (stream)
    client_instance._queues.setdefault(guild_id, [])
    if len(client_instance._queues[guild_id]) >= MAX_QUEUE_SIZE:
        try: await text_channel.send(embed=create_error_embed(f"Queue is full. Cannot add '{song_audio_info['title']}'."))
        except discord.HTTPException: pass
        return

    song_to_add = {
        'webpage_url': song_audio_info['webpage_url'], 
        'title': song_audio_info['title'],
        'duration': song_audio_info.get('duration'), 
        'thumbnail': song_audio_info.get('thumbnail'),
        'uploader': song_audio_info.get('uploader'), 
        'requester': message.author.mention, # User who posted the link
        'stream_url': song_audio_info['url'] # This is the direct playable stream
    }
    client_instance._queues[guild_id].append(song_to_add)
    await client_instance.save_guild_settings_to_file(guild_id)

    # Corrected line below:
    add_embed = discord.Embed(
        title="🎵 Added to Queue (from Link)",
        description=f"[{truncate_text(song_to_add['title'],70)}]({song_to_add['webpage_url']})", # Added description
        color=discord.Color.green()
    )
    add_embed.add_field(name="Position", value=str(len(client_instance._queues[guild_id])))
    add_embed.add_field(name="Duration", value=format_duration(song_to_add['duration']))
    if song_to_add.get('thumbnail'):
        add_embed.set_thumbnail(url=song_to_add['thumbnail'])

    try:
        await text_channel.send(embed=add_embed)
    except discord.HTTPException as e:
        print(f"DEBUG EMBED_INIT: Error sending 'Added to Queue' message: {e}")
        pass # Or handle more specifically

    print(f"DEBUG EMBED_INIT: Successfully processed and queued: '{song_to_add.get('title')}'") # E8

    # 5. Start playback if not already playing
    if not vc.is_playing() and not client_instance._current_song.get(guild_id) and client_instance._queues.get(guild_id):
        print(f"DEBUG EMBED_INIT: VC not playing and queue has items. Calling _play_guild_queue for guild {guild_id}")
        await client_instance._play_guild_queue(guild_id)
    elif guild_id in client_instance._leave_tasks: 
        print(f"DEBUG EMBED_INIT: Cancelling leave task for guild {guild_id} as new song added from embed.")
        client_instance._leave_tasks[guild_id].cancel()
        client_instance._leave_tasks.pop(guild_id, None)
    else:
        print(f"DEBUG EMBED_INIT: VC already playing or current song exists. Not calling _play_guild_queue. VC Playing: {vc.is_playing()}, Current Song Exists: {bool(client_instance._current_song.get(guild_id))}")

# This assumes 'client' is your globally defined MyClient instance.
# If on_message is a method of MyClient, replace 'client' with 'self'
# and remove the 'client_instance' parameter from _initiate_play_from_embed if it becomes a method.

@client.event
async def on_message(message: discord.Message):
    # Use 'client' for attributes like client.user.id, client._pending_text_searches
    # If on_message is a method of MyClient, use 'self' instead of 'client'.

    print(f"\nDEBUG ON_MESSAGE: START. Msg ID: {message.id}, Content: '{truncate_text(message.content, 70)}' from {message.author.name}")

    if message.author.bot:
        print("DEBUG ON_MESSAGE: Msg from bot, ignoring.")
        return
        
    if not message.guild:
        print("DEBUG ON_MESSAGE: Msg not in guild. Skipping music logic.")
        return

    content_strip = message.content.strip()
    content_lower = content_strip.lower()
    
    # --- UNIFIED SPOTIFY EMBED HANDLING ---
    # This block will now handle ANY message containing a Spotify link,
    # whether it's a bare link or part of a command.
    if "open.spotify.com/" in content_lower:
        print(f"DEBUG ON_MESSAGE: Spotify link detected in message. Waiting for embed...")
        
        # Give Discord time to generate the embed. This is a heuristic delay.
        await asyncio.sleep(1.8) 
        
        refetched_message = None
        try:
            refetched_message = await message.channel.fetch_message(message.id)
            print(f"DEBUG ON_MESSAGE: Refetched message for Spotify link. Has embeds: {bool(refetched_message.embeds)}")
        except (discord.NotFound, discord.HTTPException) as e:
            print(f"DEBUG ON_MESSAGE: Failed to refetch message ID {message.id}: {e}. Will use original message (embeds might be missing).")
            refetched_message = message

        if refetched_message and refetched_message.embeds:
            embed = refetched_message.embeds[0]
            
            # Ensure the embed is actually from Spotify before proceeding
            if embed.provider and embed.provider.name and "Spotify" in embed.provider.name:
                print(f"DEBUG ON_MESSAGE: Confirmed Spotify embed. Provider: {embed.provider.name}, Title: '{embed.title}'")
                
                # --- THOROUGH METADATA EXTRACTION FROM EMBED ---
                song_title, artist_name = None, None
                raw_embed_title = embed.title or ""
                raw_embed_description = embed.description or ""
                # Author can sometimes be the artist, playlist owner, or album artist
                raw_embed_author_name = (embed.author.name if embed.author and embed.author.name else "")
                
                # Attempt 1: Parse from embed.title (e.g., "Song Title • Artist")
                if raw_embed_title:
                    parts = raw_embed_title.split("•", 1)
                    song_title = parts[0].strip()
                    if len(parts) > 1:
                        artist_name = parts[1].strip()
                
                # Attempt 2: Parse artist from embed.description (e.g., "Song by Artist")
                if not artist_name and raw_embed_description:
                    match_by = re.search(r"(?:song|album|ep|track)\s+by\s+([^•\n(]+)", raw_embed_description, re.IGNORECASE)
                    if match_by:
                        potential_artist = match_by.group(1).strip()
                        if not artist_name or (potential_artist and len(potential_artist) > len(artist_name or "")):
                            artist_name = potential_artist
                
                # Attempt 3: Use embed.author.name as a fallback if it's not the same as the title
                if not artist_name and raw_embed_author_name:
                    if raw_embed_author_name.lower() != (song_title or "").lower():
                        artist_name = raw_embed_author_name
                
                # Clean up common suffixes like "and X more artists"
                if artist_name:
                    artist_name = re.sub(r"\s+and \d+ more(?: artists)?$", "", artist_name, flags=re.IGNORECASE).strip(" .,;-")

                if song_title:
                    search_terms = [song_title]
                    if artist_name and artist_name.lower() != "various artists":
                        search_terms.append(artist_name)
                    
                    # Form the YouTube search query
                    derived_query = f"ytsearch:{' '.join(search_terms)} audio"
                    print(f"DEBUG ON_MESSAGE: EMBED PARSED. Title: '{song_title}', Artist: '{artist_name}'. Derived YT Query: '{derived_query}'")
                    
                    # Call the helper to handle playback
                    await _initiate_play_from_embed(client, refetched_message, derived_query)
                    
                    print(f"DEBUG ON_MESSAGE: Spotify link handled by embed. RETURNING to prevent command processing for MSG ID {message.id}.")
                    return # CRITICAL: Stop further processing of this message
                else:
                    print(f"DEBUG ON_MESSAGE: Spotify embed found, but FAILED to extract a song title. Passing to command system as a fallback.")

            else:
                print(f"DEBUG ON_MESSAGE: Embed found, but provider is not Spotify. Passing to command system.")
        else:
            print(f"DEBUG ON_MESSAGE: No embeds found for Spotify link message. Passing to command system as a fallback.")

    # --- Fallback for non-Spotify messages or failed embed processing ---

    # Text Search Selection Logic (to prevent command processing for number replies)
    if message.content.isdigit() and message.author.id in client._pending_text_searches:
        # ... (Your existing logic to check if it's a valid selection number) ...
        pending_data = client._pending_text_searches.get(message.author.id)
        if pending_data and message.channel.id == pending_data.get('channel_id'):
            try:
                if 1 <= int(message.content) <= len(pending_data.get('results', [])):
                    print(f"DEBUG ON_MESSAGE: Detected pending text search selection. Letting wait_for handle.")
                    return
            except (ValueError, KeyError): pass

    # If not handled by embed logic, process as a potential command
    print(f"DEBUG ON_MESSAGE: Reached end of on_message, calling client.process_commands for: '{content_strip}'")
    await client.process_commands(message)

@client.event
async def on_voice_state_update(member: discord.Member, before: discord.VoiceState, after: discord.VoiceState):
    if not member.guild: return # Should not happen with voice state updates
    guild_id = member.guild.id
    vc = client._voice_clients.get(guild_id)

    if member.id == client.user.id and before.channel and not after.channel: # Bot was disconnected
        print(f"Bot was disconnected from VC in guild {guild_id} ({member.guild.name}).")
        
        # Clean up interactive NP message if it exists for this guild
        if client._interactive_np_message_ids.get(guild_id) and client._last_text_channel.get(guild_id):
            try:
                old_np_msg = await client._last_text_channel[guild_id].fetch_message(client._interactive_np_message_ids[guild_id])
                await old_np_msg.delete()
            except (discord.NotFound, discord.HTTPException): pass
            client._interactive_np_message_ids.pop(guild_id, None)

        if client.get_guild_24_7_mode(guild_id) and before.channel: # If 24/7 mode and was in a channel
            print(f"24/7 mode active for guild {guild_id}. Attempting to rejoin {before.channel.name}.")
            await asyncio.sleep(3) # Short delay before attempting rejoin
            try:
                new_vc = await before.channel.connect(timeout=15.0, reconnect=True)
                client._voice_clients[guild_id] = new_vc
                print(f"Successfully rejoined {before.channel.name} for 24/7 mode in guild {guild_id}.")
                # If queue exists or genre autoplay is set, try to resume/start playback
                if (client._queues.get(guild_id) or client.get_guild_autoplay_genre(guild_id)) and not new_vc.is_playing():
                    await client._play_guild_queue(guild_id)
            except Exception as e:
                print(f"Failed to rejoin {before.channel.name} for 24/7 mode in guild {guild_id}: {e}")
                await client.disconnect_voice(guild_id) # Full cleanup if rejoin fails
        else: # Not 24/7 mode or no channel to rejoin, perform full cleanup
            await client.disconnect_voice(guild_id) # Saves state and cleans client-side objects
        return

    if vc and vc.channel == before.channel: # User action in the bot's current channel
        if client.get_guild_24_7_mode(guild_id):
            if guild_id in client._leave_tasks: client._leave_tasks[guild_id].cancel(); client._leave_tasks.pop(guild_id, None)
            return

        non_bot_members_in_vc = [m for m in vc.channel.members if not m.bot]
        is_inactive_for_leave = not vc.is_playing() and not client._queues.get(guild_id) and not client._current_song.get(guild_id) and client.get_guild_loop_mode(guild_id) == "off"

        if not non_bot_members_in_vc: # Bot is alone
            if is_inactive_for_leave and (guild_id not in client._leave_tasks or client._leave_tasks.get(guild_id, asyncio.Future()).done()):
                if client._last_text_channel.get(guild_id):
                    try: await client._last_text_channel[guild_id].send(f"🤖 I'm alone and inactive in {vc.channel.mention}. I'll leave in {AUTO_LEAVE_DELAY // 60} minutes if nobody joins or plays something.")
                    except discord.HTTPException: pass
                await client.schedule_leave(guild_id)
        # Check if users are present but bot is inactive
        elif non_bot_members_in_vc and is_inactive_for_leave:
             if guild_id not in client._leave_tasks or client._leave_tasks.get(guild_id, asyncio.Future()).done():
                if client._last_text_channel.get(guild_id):
                    try: await client._last_text_channel[guild_id].send(f"🤖 I'm inactive in {vc.channel.mention}. I'll leave in {AUTO_LEAVE_DELAY // 60} minutes if nothing is played.")
                    except discord.HTTPException: pass
                await client.schedule_leave(guild_id)
        elif non_bot_members_in_vc and guild_id in client._leave_tasks and not client._leave_tasks[guild_id].done(): # Users present, cancel leave if active
            client._leave_tasks[guild_id].cancel(); client._leave_tasks.pop(guild_id, None)

@client.event
async def on_interaction(interaction: discord.Interaction):
    if interaction.type == discord.InteractionType.component:
        custom_id = interaction.data.get("custom_id", "")
        
        # ---- REMOVE OR COMMENT OUT THIS ENTIRE BLOCK ----
        # if custom_id.startswith("np_"): 
        #     try:
        #         # This logic is no longer needed for decorated buttons in NowPlayingView
        #         # action_guild_id_str = custom_id.split("_")[-1] # OLD LOGIC
        #         # action_guild_id = int(action_guild_id_str)    # OLD LOGIC
                
        #         # if action_guild_id != interaction.guild_id:
        #         #     if not interaction.response.is_done():
        #         #         await interaction.response.send_message("Button interaction mismatch (guild).", ephemeral=True)
        #         #     else:
        #         #         await interaction.followup.send("Button interaction mismatch (guild).", ephemeral=True)
        #         #     return
                
        #         # discord.py handles dispatch to the correct decorated button callback in NowPlayingView automatically.
        #         # No explicit parsing or calling needed here.
        #         pass

        #     except (IndexError, ValueError) as e:
        #         print(f"Error parsing NP button custom_id '{custom_id}': {e}") # This error should no longer occur
        #         if not interaction.response.is_done(): # Check before sending
        #             await interaction.response.send_message("Error processing button command.", ephemeral=True)
        #         # else: # If already responded, can't send another main response. Log it or followup.
        #         #     await interaction.followup.send("Error processing button command (followup).", ephemeral=True)

        #     # IMPORTANT: Do not return here unconditionally if you have other component types to handle below.
        #     # However, for np_ buttons, since discord.py handles them, we don't need this block.
        #     # If you were to keep this block for some reason, you'd `return` only if it was an np_ button.
        #     # But it's better to remove it.
        # ---- END OF BLOCK TO REMOVE/COMMENT ----

        # Handle VoteSkip Button (This logic is fine as it's for dynamically created buttons)
        if custom_id.startswith("internal_voteskip_yes_"): # Use elif if the above block is commented, if it's removed then `if` is fine.
            guild_id = interaction.guild_id
            try: vote_message_id = int(custom_id.split("_")[-1])
            except ValueError: await interaction.response.send_message("Invalid vote button ID.", ephemeral=True); return
            
            if not interaction.message or interaction.message.id != vote_message_id:
                await interaction.response.send_message("This vote button does not match the poll message.", ephemeral=True); return

            vote_poll_user_ids = client._vote_skips.get(guild_id, {}).get(vote_message_id) # This is List[int]
            if not vote_poll_user_ids: # Poll expired or already processed
                await interaction.response.send_message("This voteskip poll is no longer active.", ephemeral=True); return

            vc = client._voice_clients.get(guild_id)
            if not vc or not interaction.user.voice or interaction.user.voice.channel != vc.channel:
                 await interaction.response.send_message("You must be in the bot's voice channel to vote.", ephemeral=True); return
            
            if interaction.user.id in vote_poll_user_ids:
                await interaction.response.send_message("You have already voted in this poll.", ephemeral=True); return

            await interaction.response.defer() # Acknowledge interaction
            client._vote_skips[guild_id][vote_message_id].append(interaction.user.id)
            
            listeners_in_vc = [m for m in vc.channel.members if not m.bot and m.voice and m.voice.channel == vc.channel]
            required_votes = max(1, int(len(listeners_in_vc) * VOTE_SKIP_PERCENTAGE)) if listeners_in_vc else 1
            current_votes = len(client._vote_skips[guild_id][vote_message_id])
            
            try:
                original_embed = interaction.message.embeds[0]; new_embed = original_embed.copy()
                field_updated = False
                for i, field in enumerate(new_embed.fields): # Update existing "Votes" field
                    if field.name and field.name.lower() == "votes":
                        new_embed.set_field_at(i, name="Votes", value=f"{current_votes} / {required_votes}", inline=False); field_updated = True; break
                if not field_updated: # Should not happen if embed was created correctly
                    new_embed.add_field(name="Votes", value=f"{current_votes} / {required_votes}", inline=False)
                await interaction.message.edit(embed=new_embed)
            except Exception as e: print(f"Error updating voteskip message embed: {e}")

            if current_votes >= required_votes:
                current_song_at_vote_pass = client._current_song.get(guild_id) # Song at the moment vote passes
                if vc.is_connected() and current_song_at_vote_pass:
                    skipped_title = current_song_at_vote_pass.get('title', 'Current song')
                    if guild_id in client._up_next_tasks: client._up_next_tasks[guild_id].cancel(); client._up_next_tasks.pop(guild_id, None)
                    client._is_processing_next_song[guild_id] = False; vc.stop() # Trigger next song
                    
                    await interaction.followup.send(f"🗳️ Vote passed! Skipping **{truncate_text(skipped_title,60)}**.", ephemeral=False) # Public message
                    client._vote_skips[guild_id].pop(vote_message_id, None) # Remove poll
                    try: # Disable buttons on poll message
                        # Re-fetch view to ensure it's the current one
                        view_from_message = View.from_message(interaction.message)
                        if view_from_message: 
                            for item_btn in view_from_message.children:
                                if isinstance(item_btn, Button): item_btn.disabled = True
                            final_embed = new_embed.copy(); final_embed.description += "\n\n**Vote passed! Song skipped.**"; final_embed.color = discord.Color.green()
                            await interaction.message.edit(embed=final_embed, view=view_from_message)
                    except Exception as e_view: print(f"Error disabling vote view after pass: {e_view}")
                else: # Song might have ended or bot disconnected during vote
                    await interaction.followup.send("Vote passed, but the song already ended or playback was stopped.", ephemeral=True)
                    client._vote_skips[guild_id].pop(vote_message_id, None)
        # End of voteskip button specific logic
    # End of component interaction type
    # If not a component interaction handled above, or other interaction types, discord.py handles them (e.g., slash commands)

# --- BOT STARTUP ---
if __name__ == "__main__":
    if not BOT_TOKEN:
        print("CRITICAL: Bot token not configured. Set DISCORD_BOT_TOKEN environment variable.")
    else:
        try:
            client.run(BOT_TOKEN)
        except discord.errors.PrivilegedIntentsRequired as e:
            print(f"ERROR: Privileged Intents Required: {e}\nPlease enable Presence, Server Members, and Message Content Intents for your bot in the Discord Developer Portal.")
        except discord.errors.LoginFailure:
            print("ERROR: Login Failed. Please ensure your bot token is correct and valid.")
        except Exception as e:
            print(f"An unexpected error occurred during bot startup or runtime: {type(e).__name__} - {e}")
            traceback.print_exc()
