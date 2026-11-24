-- Prove2me | solution 1 for GlobalTheory.ClassParam.Intw.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:28:50.999793+00:00
-- url     : https://prove2.me/submissions/f5b35741-66f0-4385-9ded-49204a3bb977

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_mulUnit_apply
import Theorems.Thm_GlobalTheory_ClassParam_mulUnit_symm_apply

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
namespace Intw
theorem _root_.solution {g : Matrix (Fin r) (Fin r) A} {φ : B ≃ₗ[A] (Fin r → A)} (h : Intw α g φ)
    (z : Bˣ) : Intw α g (mulUnit A z ≪≫ₗ φ) := by
  intro u
  rw [h]
  simp only [LinearEquiv.trans_apply, mulUnit_apply, LinearEquiv.symm_trans_apply,
    mulUnit_symm_apply]
  congr 1
  rw [mul_left_comm α, Units.mul_inv_cancel_left]
end Intw
end GlobalTheory.ClassParam
