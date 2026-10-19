-- Prove2me | solution 1 for OAI.CirculantHadamard.BinaryBlocks.fourthRoot_character_star
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:44:43.82799+00:00
-- url     : https://prove2.me/submissions/626a1142-4d82-4a7c-b39a-9e0066c73277

import Mathlib
theorem solution {S : Type*} [CommRing S] [StarRing S] (i : S) (hi : i ^ 2 = -1) (hstar : star i = -i) :
    ∀ a : ZMod 4, i ^ (-a).val = star (i ^ a.val) := by
  intro a
  rw [star_pow, hstar]
  fin_cases a
  · show i ^ 0 = (-i) ^ 0
    simp
  · show i ^ 3 = (-i) ^ 1
    rw [pow_succ, hi]; ring
  · show i ^ 2 = (-i) ^ 2
    ring
  · show i ^ 1 = (-i) ^ 3
    have : (-i) ^ 3 = -(i ^ 2 * i) := by ring
    rw [this, hi]; ring
