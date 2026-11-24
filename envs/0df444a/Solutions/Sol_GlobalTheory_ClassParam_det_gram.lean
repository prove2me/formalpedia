-- Prove2me | solution 1 for GlobalTheory.ClassParam.det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:45.52226+00:00
-- url     : https://prove2.me/submissions/659ab3d1-7445-4cf3-a316-3bb3fafc5cea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_gram_eq

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
    (gram τ x e).det = Algebra.norm A x * (gram τ 1 e).det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det e]
end GlobalTheory.ClassParam
