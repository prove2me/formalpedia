-- Prove2me | solution 1 for GlobalTheory.T.exists_least_weight_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:33.463064+00:00
-- url     : https://prove2.me/submissions/ee41d5a8-f5ae-4689-a2f7-539737c959cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsExponentStrictlyLeastWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsExponentStrictlyLeastWeightStatement
import Theorems.Thm_GlobalTheory_exists_exponent_strictly_least_weight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  first | exact @GlobalTheory.exists_exponent_strictly_least_weight | exact GlobalTheory.exists_exponent_strictly_least_weight | (intros; apply GlobalTheory.exists_exponent_strictly_least_weight <;> assumption)
end _root_.GlobalTheory.T
