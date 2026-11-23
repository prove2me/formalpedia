-- Prove2me | solution 1 for GlobalTheory.KeyKa.pointMatrix_mul_leftMulMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:22.471852+00:00
-- url     : https://prove2.me/submissions/05c45305-b0c4-4702-aeb9-ce41facb9f54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution {O B Ix : Type} [CommRing O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)) (y : B) :
    (Matrix.of fun a a' => e a (β a')) * Algebra.leftMulMatrix β y
      = Matrix.diagonal (fun a => e a y) * (Matrix.of fun a a' => e a (β a')) := by
  ext a a'
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [Matrix.of_apply, Algebra.leftMulMatrix_eq_repr_mul]
  rw [← map_mul]
  conv_rhs => rw [← β.sum_repr (y * β a')]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
end GlobalTheory.KeyKa
