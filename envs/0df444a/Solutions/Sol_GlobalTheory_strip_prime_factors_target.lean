-- Prove2me | solution 1 for GlobalTheory.strip_prime_factors_target
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:16.022701+00:00
-- url     : https://prove2.me/submissions/6c2a3b98-18db-455b-ae1e-659e039b9c29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactors
import Theorems.Thm_GlobalTheory_strip_prime_factors

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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y :=
  fun R _ _ _ _ π J x hx => strip_prime_factors R π J x hx
end GlobalTheory
