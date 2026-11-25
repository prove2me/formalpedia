-- Prove2me | solution 1 for GlobalTheory.T.exists_strip_finitely_many_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:19:18.951029+00:00
-- url     : https://prove2.me/submissions/724eab84-11d0-4790-a2cb-53a5a777f5a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactors
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStripFinitelyManyPrimeFactorsStatement
import Theorems.Thm_GlobalTheory_strip_prime_factors_target


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (x : R), x ≠ 0 → ∃ (m : Fin n → ℕ) (y : R), x = y * ∏ j ∈ J, π j ^ m j ∧ ∀ j ∈ J, Prime (π j) → ¬ π j ∣ y := by
  first | exact @GlobalTheory.strip_prime_factors_target | exact GlobalTheory.strip_prime_factors_target | (intros; apply GlobalTheory.strip_prime_factors_target <;> assumption)
end _root_.GlobalTheory.T
