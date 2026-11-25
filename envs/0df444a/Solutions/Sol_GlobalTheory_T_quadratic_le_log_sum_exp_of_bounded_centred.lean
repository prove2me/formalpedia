-- Prove2me | solution 1 for GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:12:12.067351+00:00
-- url     : https://prove2.me/submissions/d3ee3c2d-967d-4c7d-a97b-1415a6ee373f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CumulantLowerBoundOfBoundedCentred
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CumulantLowerBoundOfBoundedCentredStatement
import Theorems.Thm_GlobalTheory_cumulant_lower_bound_of_bounded_centred


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 → ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) → min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  first | exact @GlobalTheory.cumulant_lower_bound_of_bounded_centred | exact GlobalTheory.cumulant_lower_bound_of_bounded_centred | (intros; apply GlobalTheory.cumulant_lower_bound_of_bounded_centred <;> assumption)
end _root_.GlobalTheory.T
