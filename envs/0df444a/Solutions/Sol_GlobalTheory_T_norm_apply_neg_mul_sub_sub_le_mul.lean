-- Prove2me | solution 1 for GlobalTheory.T.norm_apply_neg_mul_sub_sub_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:17.046902+00:00
-- url     : https://prove2.me/submissions/7602b7c0-d9eb-49f5-b073-a5e697fada2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalisedPeriodAlgebraicEstimate
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalisedPeriodAlgebraicEstimateStatement
import Theorems.Thm_GlobalTheory_normalisedPeriod_algebraic_estimate


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
theorem _root_.solution : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t → (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z → (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) → ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  first | exact @GlobalTheory.normalisedPeriod_algebraic_estimate | exact GlobalTheory.normalisedPeriod_algebraic_estimate | (intros; apply GlobalTheory.normalisedPeriod_algebraic_estimate <;> assumption)
end _root_.GlobalTheory.T
