-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.norm_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:22.29424+00:00
-- url     : https://prove2.me/submissions/733b7fa1-c6fc-42ba-b508-49f1ea46bb84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound
namespace GlobalTheory.WeightedInverseBound
theorem _root_.solution {m : Type} [Fintype m] {g : ℕ} {Y : Matrix m (Fin g) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j k, |Y j k| ≤ C) (z : Fin g → ℝ) :
    ‖Y.mulVec z‖ ≤ g * C * ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  calc ‖Y.mulVec z j‖ = |∑ k, Y j k * z k| := rfl
    _ ≤ ∑ k, |Y j k * z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin g, C * ‖z‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        exact mul_le_mul (h j k) (norm_le_pi_norm z k) (abs_nonneg _) hC
    _ = g * C * ‖z‖ := by simp [mul_assoc]
end GlobalTheory.WeightedInverseBound
