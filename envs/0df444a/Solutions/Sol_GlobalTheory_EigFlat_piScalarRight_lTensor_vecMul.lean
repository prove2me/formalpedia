-- Prove2me | solution 1 for GlobalTheory.EigFlat.piScalarRight_lTensor_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:04.23247+00:00
-- url     : https://prove2.me/submissions/e5451136-c414-43d3-afa8-bf39589054ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]
namespace GlobalTheory.EigFlat
theorem _root_.solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    [DecidableEq b] (U : Matrix a b A) (B : Type) [CommRing B] [Algebra A B]
    (x : B ⊗[A] (a → A)) :
    TensorProduct.piScalarRight A B B b (LinearMap.lTensor B U.vecMulLinear x)
      = (TensorProduct.piScalarRight A B B a x) ᵥ* U.map (algebraMap A B) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.add_vecMul]
  | tmul s v =>
    ext j
    simp [Matrix.vecMul, dotProduct, Algebra.smul_def, Finset.sum_mul, mul_right_comm]
end GlobalTheory.EigFlat
