-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.det_gram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:47.364805+00:00
-- url     : https://prove2.me/submissions/b22b74c3-1186-4797-be38-5901c75dc303

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_gram_change

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
    ∃ z : Aˣ, (gram τ x e').det = (gram τ x e).det * (z * σ z) := by
  have hu : IsUnit (e.toMatrix e').det := e.isUnit_det e'
  refine ⟨hu.unit, ?_⟩
  rw [S.gram_change x e e', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, IsUnit.unit_spec,
    RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]; ring
end HidaSetting
end GlobalTheory.ClassParam
