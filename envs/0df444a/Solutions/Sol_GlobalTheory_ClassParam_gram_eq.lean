-- Prove2me | solution 1 for GlobalTheory.ClassParam.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:15.967684+00:00
-- url     : https://prove2.me/submissions/45e646a8-2b92-4047-9fe2-629d71cf248d

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
theorem _root_.solution (x : B) (e : Module.Basis (Fin r) A B) :
    gram τ x e = (Algebra.leftMulMatrix e x)ᵀ * gram τ 1 e := by
  ext i j
  simp only [gram, tf, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Algebra.leftMulMatrix_eq_repr_mul, one_mul]
  conv_lhs => rw [← e.sum_repr (x * e i)]
  simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, smul_eq_mul]
end GlobalTheory.ClassParam
