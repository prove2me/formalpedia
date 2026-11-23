-- Prove2me | solution 1 for GlobalTheory.PointStepCompare.evalOn_tensorCoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:36.403142+00:00
-- url     : https://prove2.me/submissions/0187ae38-77f0-4153-bce1-488f9cc4b3a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)
namespace GlobalTheory.PointStepCompare
theorem _root_.solution (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end GlobalTheory.PointStepCompare
