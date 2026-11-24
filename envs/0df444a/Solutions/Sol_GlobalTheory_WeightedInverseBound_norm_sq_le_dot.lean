-- Prove2me | solution 1 for GlobalTheory.WeightedInverseBound.norm_sq_le_dot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:00.272282+00:00
-- url     : https://prove2.me/submissions/0a3d0d31-453c-453a-97f0-154b6805ff05

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
theorem _root_.solution {g : ℕ} (x : Fin g → ℝ) : ‖x‖ * ‖x‖ ≤ x ⬝ᵥ x := by
  have h0 : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun k _ => mul_self_nonneg _
  have : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun k => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun k => x k * x k) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ k)
  calc ‖x‖ * ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (x ⬝ᵥ x) :=
        mul_le_mul this this (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = x ⬝ᵥ x := Real.mul_self_sqrt h0
end GlobalTheory.WeightedInverseBound
