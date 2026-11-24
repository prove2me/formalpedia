-- Prove2me | solution 1 for GlobalTheory.exists_coprime_orderOf_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:04.703393+00:00
-- url     : https://prove2.me/submissions/642a2e22-eee3-4783-b2e0-0e456f25b87d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm
end GlobalTheory
