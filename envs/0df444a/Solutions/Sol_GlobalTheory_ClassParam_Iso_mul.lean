-- Prove2me | solution 1 for GlobalTheory.ClassParam.Iso.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.828872+00:00
-- url     : https://prove2.me/submissions/dca8f269-e885-442e-9e98-3c9c00df7160

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_mulUnit_apply

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
namespace Iso
theorem _root_.solution {x : B} {φ : B ≃ₗ[A] (Fin r → A)} (h : Iso σ τ J x φ) (z : Bˣ) :
    Iso σ τ J (x * (z * τ z)) (mulUnit A z ≪≫ₗ φ) := by
  intro y y'
  simp only [LinearEquiv.trans_apply, mulUnit_apply]
  rw [h]
  unfold tf
  congr 1
  rw [map_mul]; ring
end Iso
end GlobalTheory.ClassParam
