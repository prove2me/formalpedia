-- Prove2me | solution 1 for GlobalTheory.BadShare.pow_padicVal_eq_one_of_primePow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:05:28.25839+00:00
-- url     : https://prove2.me/submissions/94ec18d4-132f-4f01-9666-f95e6a7d6ed4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by
  have := Fact.mk hl
  have d1 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf y ∣ l ^ a := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 d2
  rw [hi] at d1
  have hle : i ≤ padicValNat l n := (padicValNat_dvd_iff_le hn.ne').1 d1
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  exact pow_dvd_pow l hle
end GlobalTheory.BadShare
