#![cfg_attr(not(feature = "std"), no_std)]
use sp_std::prelude::*;
use sp_std::cmp::Ordering::{
	Equal, Greater, Less
};
use core::{result, debug_assert};
use codec::{Encode, Decode};
use frame_support::{
	Parameter, decl_module, decl_event, decl_storage, decl_error, ensure,
	weights::{Weight, GetDispatchInfo, Pays},
	traits::{
		Currency, EnsureOrigin, Get, Randomness, UnfilteredDispatchable,
		OnUnbalanced, ExistenceRequirement,
	},
	dispatch::DispatchResultWithPostInfo,
};
use sp_runtime::{
	RuntimeDebug, ModuleId, DispatchResult, DispatchError,
	traits::{Hash, Zero, CheckedDiv, AccountIdConversion, SimpleBitOps, Scale},
};
use frame_frame_system::ensure_signed;
// use sr_primitives::traits::{Hash};
// use support::{decl_module, decl_storage, decl_event, StorageValue, StorageMap};
// use support::traits::{Randomness, Currency, WithdrawReasons, WithdrawReason, ExistenceRequirement};
// use support::dispatch::DispatchResult;
// use frame_system::ensure_signed;

mod naive_rsa;
mod stage;
mod cards;
mod keys;
mod ranking;

pub use stage::StageId;

pub trait Trait: frame_system::Trait + pallet_balances::Trait {
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Combination {
	pub rank: u32,
	pub high: u32,
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct WinLossInfo<Account> {
	winner: Account,
	win_hand: Combination,
	loser: Account,
	loss_hand: Combination,
}

decl_storage! {
	trait Store for Module<T: Trait> as Poker {
		///Minimal amount to bet (small and big "blinds")
		Blinds get(blinds): (T::Balance, T::Balance);

		///Maximum 2 players currently
		Dealer get(dealer): Option<T::AccountId>;
		Player get(player): Option<T::AccountId>;

		///`Idle` when game is finished or not started,
		///and `Preflop`,`Flop`,`Turn` or `River` when it is in progress
		Stage get(stage): u32;

		///Chips which are fixed after betting round and withdrawn from participants' stacks
		Pot get(pot): T::Balance;
		///Current bets of participants, can change until they are equal
		Bets get(bets): map T::AccountId => T::Balance;
		///Game balances of participants
		Stacks get(stacks): map T::AccountId => T::Balance;

		///Indicator of a participant who's turn to bet;
		///if it is `None`, that means we are waiting for the keys for next stage
		BetsNow get(bets_now): Option<T::AccountId>;

		///Current maximum bet, other players must "call" or "raise" it, or fold cards
		BetLevel get(bet_level): Option<T::Balance>;

		///This field is Some, when a game is over
		RoundResult get(round_result): Option<WinLossInfo<T::AccountId>>;

		///Key pairs generated by each participant,
		///secret parts are revealed in certain moments,
		///unlocking stages of the game or revealing cards
		Keys get(keys): map T::AccountId => keys::PublicStorage;
		Secrets get(secrets): map T::AccountId => keys::RevealedSecrets;

		///Cards which are shared among participants
		SharedCards get(shared_cards): Vec<u8>;

		///Cards "in the pocket", private and non-visible before showdown
		PocketCards get(pocket_cards): map T::AccountId => Vec<u8>;

		///Cards "in the pocket" which have been revealed by their owner
		OpenCards get(open_cards): map T::AccountId => Vec<u8>;

		///Shared cards are hidden and revealed by-stage when all
		///players submit their secret keys for corresponding stages
		FlopCards get(flop_cards): Vec<u8>;
		TurnCards get(turn_cards): Vec<u8>;
		RiverCards get(river_cards): Vec<u8>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		fn create_game(origin, buy_in: T::Balance, big_blind: T::Balance) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let dealer = Self::dealer();
			let player = Self::player();

			if dealer.is_some() || player.is_some() {
				return Self::error(who, "The game is already created, probably you can join");
			}
			if buy_in < big_blind {
				return Self::error(who, "Choose smaller blinds");
			}

			Self::announce("Dealer joins the game, waiting for a player...");
			<Dealer<T>>::put(&who);

			let small_blind = big_blind / 2_u32.into();
			<Blinds<T>>::put((small_blind, big_blind));

			Self::refill_chips(who, buy_in)
		}

		fn join_game(origin, buy_in: T::Balance) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let dealer = Self::dealer();
			if dealer.is_none() {
				return Self::error(who, "There is nobody so far, you are free to set up the game.");
			}

			let dealer = dealer.unwrap();
			if &who == &dealer {
				return Self::error(who, "Dude, you are not gonna play with yourself, right?");
			}

			let player = Self::player();
			if player.is_some() {
				return Self::error(who, "Sorry man, no room.");
			}
			let (_, minimal_amount) = Self::blinds();
			if buy_in < minimal_amount {
				return Self::error(who, "Get some money first...");
			}

			<Player<T>>::put(&who);
			Self::announce("Player joins the game! It's gonna be hot!");

			Self::refill_chips(who, buy_in)
		}

		fn leave_game_anyway(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if Self::stage() != stage::IDLE && Self::stage() != stage::SHOWDOWN {
				Self::perform_fold(who.clone())?;
			}
			Self::remove_participant(who)
		}

		fn leave_game(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let current = Self::stage();
			if current != stage::IDLE && current != stage::SHOWDOWN {
				return Self::error(who, "Can't quit while the game is in progress");
			}

			//for the case when we made a blind bet,
			//but other player haven't yet
			Self::reset_idle(&who);

			Self::remove_participant(who)
		}

		fn preflop(origin,
				pocket_key: Vec<u8>,
				flop_key: Vec<u8>,
				turn_key: Vec<u8>,
				river_key: Vec<u8>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			if Self::stacks(&who) == Self::zero() {
				return Self::error(who, "Probably enough? Otherwise, get some chips.")
			}
			if Self::keys(&who).is_initialized() {
				return Self::error(who, "For current round, preflop stage is already initialized");
			}

			Self::info(who.clone(), "Registering participant's keys for preflop stage");

			//All keys are received in big-endian format
			let keys = keys::PublicStorage {
				pocket: pocket_key,
				flop: flop_key,
				turn: turn_key,
				river: river_key
			};

			ensure!(keys.is_valid());
			<Keys<T>>::insert(&who, &keys);

			let dealer = Self::dealer();
			let player = Self::player();

			if dealer.is_none() {
				return Self::error(who, "The game is not even created (there is no dealer)");
			}
			if player.is_none() {
				return Self::error(who, "Nobody has joined to the game");
			}

			let dealer = dealer.unwrap();
			let player = player.unwrap();

			let dealer_keys = Self::keys(&dealer);
			let player_keys = Self::keys(&player);

			if dealer_keys.is_initialized() && player_keys.is_initialized() {
				let current = Self::stage();
				if current == stage::SHOWDOWN {
					Self::reset_open_state(&dealer, &player);
					Self::swap_dealer(dealer.clone(), player.clone());
				} else {
					if current != stage::IDLE {
						return Self::error(who, "You can move to Preflop only from Idle or Showdown");
					}

					//Since we can't store the state of cards deck in (visible) blocks,
					//we have to deal all cards in one atomic transaction;
					//then we encrypt flop, turn and river with public keys of all participants
					//and we encrypt pocket cards by public keys of corresponding player
					Self::info_all("Dealing cards for this round");

					//This is fake random for my proof-of-concept;
					//in future, it has to be replaced with off-chain random generation
					//also it probably can be workarounded with sending a nonce from the player
					let seed = (<randomness_collective_flip::Module<T>>::random_seed(), &who, &dealer_keys, &player_keys)
						.using_encoded(<T as frame_system::Trait>::Hashing::hash);

					let mut deck = (0..1024)
						.flat_map(|i| (seed, i).using_encoded(|x| x.to_vec())) //32 bytes
						.map(cards::from_random);

					let mut cards = vec![];
					while cards.len() < 12 {
						let card = deck.next().unwrap();
						if !cards.contains(&card) {
							cards.push(card);
						}
					}

					let player_cards = cards::encode(vec![&cards[0], &cards[2]]);
					let dealer_cards = cards::encode(vec![&cards[1], &cards[3]]);
					let flop_cards   = cards::encode(vec![&cards[5], &cards[6], &cards[7]]);
					let turn_cards   = cards::encode(vec![&cards[9]]);
					let river_cards  = cards::encode(vec![&cards[11]]);

					let player_cards = naive_rsa::encrypt(&player_cards[..], &player_keys.pocket[..])?;
					<PocketCards<T>>::insert(&player, player_cards);

					let dealer_cards = naive_rsa::encrypt(&dealer_cards[..], &dealer_keys.pocket[..])?;
					<PocketCards<T>>::insert(&dealer, dealer_cards);

					let flop_cards = naive_rsa::encrypt(&flop_cards[..], &player_keys.flop[..])?;
					let flop_cards = naive_rsa::encrypt(&flop_cards[..], &dealer_keys.flop[..])?;
					<FlopCards>::put(flop_cards);

					let turn_cards = naive_rsa::encrypt(&turn_cards[..], &player_keys.turn[..])?;
					let turn_cards = naive_rsa::encrypt(&turn_cards[..], &dealer_keys.turn[..])?;
					<TurnCards>::put(turn_cards);

					let river_cards = naive_rsa::encrypt(&river_cards[..], &player_keys.river[..])?;
					let river_cards = naive_rsa::encrypt(&river_cards[..], &dealer_keys.river[..])?;
					<RiverCards>::put(river_cards);

					Self::init_who_bets(dealer.clone(), &player);
				}

				<Stage>::put(stage::PREFLOP);
				<RoundResult<T>>::kill();
			} else {
				Self::info(who.clone(), "Waiting for other participants to deal pocket cards");
			}

			let (small_blind, big_blind) = Self::blinds();
			<BetLevel<T>>::put(big_blind.clone());

			let blind_bet = if &who == &dealer {
				small_blind
			} else {
				big_blind
			};

			<Bets<T>>::insert(&who, blind_bet);

			Ok(())
		}

		fn check(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if !Self::makes_bet_now(&who) {
				return Self::error(who, "Wait for your turn, please.");
			}

			let level = Self::bet_level();
			if let Some(current) = level {
				if current > Self::zero() && !Self::is_option_available(&who, current) {
					return Self::error(who, "There is already a bet, you can't check.");
				}
			}

			Self::perform_check(who, level.is_none())
		}

		fn call(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if !Self::makes_bet_now(&who) {
				return Self::error(who, "Wait for your turn, please.");
			}

			let level = Self::bet_level();
			if level.is_none() || level == Some(Self::zero()) {
				return Self::perform_check(who, level.is_none());
			}

			let level = level.unwrap();
			let stack = Self::stacks(&who);
			if stack <= level {
				<Bets<T>>::insert(&who, stack);
				Self::deposit_event(RawEvent::AllIn(who));

				//since there are only 2 participants, all-in means end of bets
				Self::update_pot();
				return Ok(());
			}

			<Bets<T>>::insert(&who, level);
			Self::deposit_event(RawEvent::Call(who.clone()));

			//previous move was either raise or big blind
			if Self::is_option_available(&Self::opponent(&who), level) {
				<BetsNow<T>>::put(Self::opponent(&who));
			} else {
				Self::update_pot();
			}

			Ok(())
		}

		fn raise(origin, total: T::Balance) -> DispatchResult {
			let who = ensure_signed(origin)?;
			if !Self::makes_bet_now(&who) {
				return Self::error(who, "Wait for your turn, please.");
			}

			let stack = Self::stacks(&who);
			if total > stack {
				return Self::error(who, "You don't have enough chips for such a raise.");
			}

			let level = Self::bet_level().unwrap_or(Self::zero());
			if total <= level {
				return Self::error(who, "Raise must be more than the current bet.");
			}

			if total == stack {
				Self::deposit_event(RawEvent::AllIn(who.clone()));
			} else {
				if total < level * 2_u32.into() {
					return Self::error(who, "Raise must be at least doubling the current bet.");
				}

				let diff = total - level;
				let (_, big_blind) = Self::blinds();
				if diff < big_blind {
					return Self::error(who, "Raise must be at least equal to big blind.");
				}

				Self::deposit_event(RawEvent::Raise(who.clone(), diff));
			}

			<BetLevel<T>>::put(total);
			<Bets<T>>::insert(&who, total);
			<BetsNow<T>>::put(Self::opponent(&who));
			Ok(())
		}

		fn next_stage(origin, requested_stage: u32, stage_secret: Vec<u8>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let stage = Self::stage();
			if stage != requested_stage - 1 {
				return Self::error(who, "Client's stage counter is wrong");
			}
			if stage < stage::PREFLOP {
				return Self::error(who, "Illegal request of the next stage");
			}
			let stage = requested_stage;

			if (Self::secrets(&who).retrieve(stage)?).is_some() {
				return Self::error(who, "The next stage is already initialized for this player");
			}

			Self::info(who.clone(), "Registering participant's keys for the next stage");

			<Secrets<T>>::mutate(&who, |secrets| {
				(*secrets).submit(stage, stage_secret.clone()).unwrap();
				ensure!(secrets.is_valid());
			});

			match Self::retrieve_both_secrets(who, stage_secret, stage)? {
				Some(((dealer, dealer_secret), (player, player_secret))) => {
					if stage == stage::SHOWDOWN {
						Self::announce("Revealing pocket cards");
						Self::reveal_pocket(&dealer, dealer_secret)?;
						Self::reveal_pocket(&player, player_secret)?;
						Self::reset_closed_state(&dealer, &player);
						<Stage>::put(stage);
						return Self::determine_winner(dealer, player);
					}

					Self::info_all("Revealing cards of the next stage");

					let dealer_key = Self::keys(&dealer).retrieve(stage)?;
					let player_key = Self::keys(&player).retrieve(stage)?;

					let hidden = match stage {
						stage::FLOP  => Self::flop_cards(),
						stage::TURN  => Self::turn_cards(),
						stage::RIVER => Self::river_cards(),

						_ => unreachable!()
					};

					let revealed = naive_rsa::decrypt(&hidden, &dealer_key[..], &dealer_secret[..])?;
					let mut revealed = naive_rsa::decrypt(&revealed, &player_key[..], &player_secret[..])?;
					Self::validate_revealed_cards(stage, &revealed[..])?;
					<SharedCards>::mutate(|v| v.append(&mut revealed));

					Self::init_who_bets(player, &dealer);
					<Stage>::put(stage);
					Ok(())
				},
				None => {
					//Technically, if we use commutative encryption, then we can
					//remove one layer of encryption after each player submits his secret
					//for current stage. Also we can do it in current implementation
					//after receiving dealer's secret (because his secret is last of applied),
					//but for simplicity we wait for all in PoC
					Self::info_all("Waiting for all participants to deal next stage");
					Ok(())
				}
			}
		}

		fn fold(origin) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::perform_fold(who)
		}
	}
}


decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId,
							Balance = <T as pallet_balances::Trait>::Balance {
		///Auxiliary events; they are redundant and not necessary,
		///but provide better user experience
		Announcement(Vec<u8>),
		InfoMessage(Option<AccountId>, Vec<u8>),
		ErrorMessage(Option<AccountId>, Vec<u8>),

		NewParticipant(AccountId, Balance),
		NewDealer(AccountId),
		ParticipantLeft(AccountId),

		Call(AccountId),
		Check(AccountId),
		Raise(AccountId, Balance),
		AllIn(AccountId),
		Fold(AccountId),

		BetsAreMade(),
	}
);

impl<T: Trait> Module<T> {

	fn refill_chips(who: T::AccountId, buy_in: T::Balance) -> DispatchResult {
		let _ = <pallet_balances::Module<T> as Currency<_>>::withdraw(
			&who, buy_in, WithdrawReasons::from(WithdrawReason::Transfer),
			ExistenceRequirement::KeepAlive)?;

		<Stacks<T>>::insert(&who, &buy_in);
		Self::deposit_event(RawEvent::NewParticipant(who, buy_in));
		Ok(())
	}

	fn reveal_pocket(who: &T::AccountId, pocket_secret: Vec<u8>) -> DispatchResult {
		let pocket_key  = Self::keys(who).pocket;
		let encrypted = Self::pocket_cards(who);
		let decrypted = naive_rsa::decrypt(&encrypted, &pocket_key[..], &pocket_secret[..])?;

		<OpenCards<T>>::insert(who, decrypted);
		Ok(())
	}

	fn perform_check(who: T::AccountId, first_check: bool) -> DispatchResult {
		if first_check {
			<BetsNow<T>>::put(Self::opponent(&who));
			<BetLevel<T>>::put(Self::zero());
		} else {
			//since there are only 2 participants, we are last who checks
			<BetsNow<T>>::kill();
			Self::update_pot();
		}

		Self::deposit_event(RawEvent::Check(who));
		Ok(())
	}

	fn perform_fold(who: T::AccountId) -> DispatchResult {
		let dealer = Self::dealer().unwrap();
		let player = Self::player().unwrap();

		let prize = Self::calculate_pot(true);

		let winner = if who == dealer { &player } else { &dealer };
		{
			let prize = prize.clone();
			<Stacks<T>>::mutate(winner, move |v| *v += prize);
		}

		Self::deposit_event(RawEvent::Fold(who));
		Self::reset_closed_state(&dealer, &player);
		Self::reset_open_state(&dealer, &player);
		Self::swap_dealer(dealer, player);
		<Stage>::kill();
		Ok(())
	}

	fn remove_participant(who: T::AccountId) -> DispatchResult {
		//This version is for 2 participants maximum;
		//and no game can contain only a player without a dealer,
		//so either we remove the player, or replace the dealer
		let player = Self::player();
		let target = Some(who.clone());

		let stack = <Stacks<T>>::take(&who);
		let _ = <pallet_balances::Module<T> as Currency<_>>::deposit_into_existing(&who, stack)?;

		if player != target {
			if Self::dealer() != target {
				return Self::error(who, "The account is not a participant of this game");
			}
			if let Some(player) = player {
				Self::deposit_event(RawEvent::NewDealer(player.clone()));
				<Dealer<T>>::put(player);
			} else {
				<Dealer<T>>::kill();
			};
		}
		<Player<T>>::kill();
		<Stage>::kill();

		Self::deposit_event(RawEvent::ParticipantLeft(who));

		Ok(())
	}

	fn determine_winner(dealer: T::AccountId, player: T::AccountId) -> DispatchResult {
		let shared_cards = cards::decode(&Self::shared_cards());
		let mut dealer_cards = cards::decode(&Self::open_cards(&dealer));
		let mut player_cards = cards::decode(&Self::open_cards(&player));
		ensure!(shared_cards.len() == 5);
		ensure!(dealer_cards.len() == 2);
		ensure!(player_cards.len() == 2);

		let mut seven = shared_cards;
		seven.append(&mut dealer_cards);
		let dealer_hand = ranking::choose_strongest_five(&seven[..]);

		seven.remove(6);
		seven.remove(5);

		seven.append(&mut player_cards);
		let player_hand = ranking::choose_strongest_five(&seven[..]);

		let result = match dealer_hand.cmp(&player_hand) {
			Greater => WinLossInfo {
				winner: dealer,
				win_hand: Combination::from(dealer_hand.combination),
				loser: player,
				loss_hand: Combination::from(player_hand.combination)
			},
			Less => WinLossInfo {
				winner: player,
				win_hand: Combination::from(player_hand.combination),
				loser: dealer,
				loss_hand: Combination::from(dealer_hand.combination)
			},
			Equal => unimplemented!() //todo: pot split
		};

		let prize = Self::calculate_pot(false);
		<Stacks<T>>::mutate(&result.winner, move |v| *v += prize);

		<RoundResult<T>>::put(result);
		Ok(())
	}

	fn validate_revealed_cards(stage: u32, cards: &[u8]) -> DispatchResult {
		let cards = cards::decode(cards);
		let amount = cards.len();
		if !cards.into_iter().all(|card| card.is_valid()) {
			return Self::error_all("Critical error: decrypted cards are invalid!");
		}
		match stage {
			stage::FLOP => if amount != 3 {
				return Self::error_all("Critical error: Flop must produce 3 cards!");
			},
			stage::TURN => if amount != 1 {
				return Self::error_all("Critical error: Turn must produce 1 card!");
			},
			stage::RIVER => if amount != 1 {
				return Self::error_all("Critical error: River must produce 1 card!");
			},
			_ => return Self::error_all("Wrong stage requested")
		}
		Ok(())
	}

	//after prototype stabilization, only necessary events must be emitted
	fn error(who: T::AccountId, message: &'static str) -> DispatchResult {
		let bytes = message.as_bytes().to_vec();
		Self::deposit_event(RawEvent::ErrorMessage(Some(who), bytes));
		Err(message)
	}

	fn info(who: T::AccountId, message: &'static str) {
		let bytes = message.as_bytes().to_vec();
		Self::deposit_event(RawEvent::InfoMessage(Some(who), bytes));
	}

	fn error_all(message: &'static str) -> DispatchResult {
		let bytes = message.as_bytes().to_vec();
		Self::deposit_event(RawEvent::ErrorMessage(None, bytes));
		Err(message)
	}

	fn info_all(message: &'static str) {
		let bytes = message.as_bytes().to_vec();
		Self::deposit_event(RawEvent::InfoMessage(None, bytes));
	}

	fn announce(message: &'static str) {
		let bytes = message.as_bytes().to_vec();
		Self::deposit_event(RawEvent::Announcement(bytes));
	}

	///Auxiliary functions

	fn zero() -> T::Balance {
		0_u32.into()
	}

	fn opponent(who: &T::AccountId) -> T::AccountId {
		let dealer = Self::dealer().unwrap();

		if &dealer == who {
			Self::player().unwrap()
		} else {
			dealer
		}
	}

	fn init_who_bets(target: T::AccountId, other: &T::AccountId) {
		//for 2 participants version, this is simple
		if Self::stacks(&target) != Self::zero() &&
			Self::stacks(other) != Self::zero() {
				<BetsNow<T>>::put(target);
		} else {
			debug_assert!(Self::bets_now().is_none())
		}
	}

	fn calculate_pot(after_fold: bool) -> T::Balance {
		let dealer = Self::dealer().unwrap();
		let player = Self::player().unwrap();

		let d_bet = <Bets<T>>::take(&dealer);
		let p_bet = <Bets<T>>::take(&player);
		Self::finish_bets(after_fold);

		<Stacks<T>>::mutate(&dealer, |v| *v -= d_bet);
		<Stacks<T>>::mutate(&player, |v| *v -= p_bet);

		<Pot<T>>::take() + d_bet + p_bet
	}

	fn finish_bets(after_fold: bool) {
		<BetsNow<T>>::kill();
		if !after_fold {
			Self::deposit_event(RawEvent::BetsAreMade());
		}
	}

	fn update_pot() {
		let pot = Self::calculate_pot(false);
		<Pot<T>>::put(pot);
		<BetLevel<T>>::kill();
	}

	fn makes_bet_now(who: &T::AccountId) -> bool {
		let expected = Self::bets_now();
		expected.is_some() && who == &expected.unwrap()
	}

	///Special rule in Poker
	fn is_option_available(who: &T::AccountId, level: T::Balance) -> bool {
		if Self::stage() != stage::PREFLOP {
			return false;
		}
		let (_, big_blind) = Self::blinds();
		if level != big_blind {
			return false;
		}

		who == &Self::player().unwrap()
	}

	fn retrieve_both_secrets(who: T::AccountId, secret: Vec<u8>, stage: StageId)
		-> result::DispatchResult<
				Option<((T::AccountId, Vec<u8>), (T::AccountId, Vec<u8>))>,
				&'static str> {
		let dealer = Self::dealer().unwrap();
		if &who == &dealer {
			let other = Self::player().unwrap();
			let other_secret = Self::secrets(&other).retrieve(stage)?;
			Ok(other_secret.map(|other_secret|
				((who, secret), (other, other_secret))))
		} else {
			let other = dealer;
			let other_secret = Self::secrets(&other).retrieve(stage)?;
			Ok(other_secret.map(|other_secret|
				((other, other_secret), (who, secret))))
		}
	}

	fn reset_idle(who_waits: &T::AccountId) {
		<Bets<T>>::remove(who_waits);

		Self::dealer().into_iter().for_each(<Keys<T>>::remove);
		Self::player().into_iter().for_each(<Keys<T>>::remove);
	}

	fn reset_closed_state(dealer:& T::AccountId, player: &T::AccountId) {
		vec![dealer, player]
			.iter().for_each(|k| {
			<Keys<T>>::remove(*k);
			<Secrets<T>>::remove(*k);
			<PocketCards<T>>::remove(*k);
		});

		<FlopCards>::kill();
		<TurnCards>::kill();
		<RiverCards>::kill();
		<BetsNow<T>>::kill();
	}

	fn reset_open_state(dealer: &T::AccountId, player: &T::AccountId) {
		<OpenCards<T>>::remove(dealer);
		<OpenCards<T>>::remove(player);
		<SharedCards>::kill();
		<RoundResult<T>>::kill();
	}

	fn swap_dealer(dealer: T::AccountId, player: T::AccountId) {
		<Dealer<T>>::put(player);
		<Player<T>>::put(dealer);
	}

}

impl Combination {
	fn from(combination: ranking::Combination) -> Self {
		Self {
			rank: combination.rank.into(),
			high: combination.high.into()
		}
	}
}

//todo: implement `Encode` and `Decode` for `Card`
//todo: put `RankedHand` instead of `Combination` into `WinLossInfo`

//todo: proper input-output of money to the game:
//1. reserve balance instead of withdrawal at the moment of joining
//2. unreserve balance + deposit/withdraw difference when leaving

//todo: optimize