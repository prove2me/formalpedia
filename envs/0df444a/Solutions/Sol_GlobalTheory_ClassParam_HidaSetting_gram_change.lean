-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.gram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:13.090053+00:00
-- url     : https://prove2.me/submissions/6855aebe-d004-40f2-a711-3d5be3308fdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
variable {σ : A →+* A} {τ : B →+* B} {α : B} {b : Module.Basis (Fin r) A B}
  {J : Matrix (Fin r) (Fin r) A}
namespace GlobalTheory.ClassParam
namespace HidaSetting
theorem _root_.solution (S : HidaSetting σ τ α b) (x : B) (e e' : Module.Basis (Fin r) A B) :
    gram τ x e' = (e.toMatrix e')ᵀ * gram τ x e * (e.toMatrix e').map σ := by
  ext i j
  simp only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Module.Basis.toMatrix_apply]
  conv_lhs => rw [← e.sum_repr (e' i), ← e.sum_repr (e' j)]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have : x * (e.repr (e' i) q • e q) * τ (e.repr (e' j) p • e p)
      = (e.repr (e' i) q * σ (e.repr (e' j) p)) • (x * e q * τ (e p)) := by
    simp only [Algebra.smul_def, map_mul, S.comp]; ring
  rw [this, map_smul, smul_eq_mul]; ring
end HidaSetting
end GlobalTheory.ClassParam
