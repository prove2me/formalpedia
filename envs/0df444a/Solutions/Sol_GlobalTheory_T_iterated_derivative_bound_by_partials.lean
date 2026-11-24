-- Prove2me | solution 1 for GlobalTheory.T.iterated_derivative_bound_by_partials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:50.457798+00:00
-- url     : https://prove2.me/submissions/d24d16a3-5279-4108-82c9-444ed263ceb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
import Theorems.Thm_GlobalTheory_norm_iteratedFDeriv_succ_le_sum_partial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by
  first | exact @GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial | exact GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial | (intros; apply GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial <;> assumption)
end _root_.GlobalTheory.T
