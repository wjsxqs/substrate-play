#![allow(dead_code)]

use sp_std::prelude::*;
// use core::debug_assert;
use frame_support::ensure;

pub type Nominal = u8;

pub const J: Nominal = 11;
pub const Q: Nominal = 12;
pub const K: Nominal = 13;
pub const A: Nominal = 1;

pub type Suit = u8;

pub const HEARTS:   Suit = 2;
pub const CLUBS:    Suit = 3;
pub const DIAMONDS: Suit = 4;
pub const SPADES:   Suit = 1;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct Card {
    pub nominal: Nominal,
    pub suit: Suit
}

impl Card {
    pub fn is_valid(&self) -> bool {
        debug_assert!(self.nominal >= 1 && self.nominal <= 13);
        debug_assert!(self.suit >= 1 && self.suit <= 4);

        self.nominal >= 1 && self.nominal <= 13
            && self.suit >= 1 && self.suit <= 4
    }
}

pub fn hearts(n: Nominal) -> Card {
    Card { nominal: n, suit: HEARTS }
}

pub fn clubs(n: Nominal) -> Card {
    Card { nominal: n, suit: CLUBS }
}

pub fn diamonds(n: Nominal) -> Card {
    Card { nominal: n, suit: DIAMONDS }
}

pub fn spades(n: Nominal) -> Card {
    Card { nominal: n, suit: SPADES }
}

pub fn encode(cards: Vec<&Card>) -> Vec<u8> {
    cards.into_iter()
        .map(|card| {
            card.is_valid();
            vec![card.nominal, card.suit]
        })
        .flatten()
        .collect()
}

pub fn decode(bytes: &[u8]) -> Vec<Card> {
    bytes.chunks(2)
        .map(|pair| Card {
            nominal: pair[0],
            suit: pair[1]
        })
        .collect()
}

//a bit unfair random generation, because 16 % 13 != 0
pub fn from_random(byte: u8) -> Card {
    let high = byte >> 4;
    let low  = byte & 15;
    debug_assert!(byte == low + high * 16);

    let card = Card {
        nominal: high % 13 + 1,
        suit: low % 4 + 1,
    };

    card.is_valid();
    card
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate_from_random() {
        assert!(from_random(3) == diamonds(A));
        assert!(from_random(16) == spades(2));
        assert!(from_random(211) == diamonds(A));
        assert!(from_random(224) == spades(2));

        assert!(from_random(0  << 4) == spades(A));
        assert!(from_random(12 << 4) == spades(K));

        assert!(from_random(13 << 4) == spades(A));
        assert!(from_random(14 << 4) == spades(2));
        assert!(from_random(15 << 4) == spades(3));
        //this means that A, 2 and 3 are a bit more frequent
    }
}