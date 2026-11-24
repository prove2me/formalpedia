-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.exists_intw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:10.249522+00:00
-- url     : https://prove2.me/submissions/5a4e71f3-f412-474a-91d3-36768f2f97ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_exists_UJ
import Theorems.Thm_GlobalTheory_ClassParam_Iso_mul
import Theorems.Thm_GlobalTheory_ClassParam_Intw_mul

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
theorem _root_.solution (S : HidaSetting σ τ α b) {x : B} {φ : B ≃ₗ[A] (Fin r → A)}
    (h : Iso σ τ J x φ) :
    ∃ g : UJ σ J, Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ := by
  let a : Bˣ := ⟨α, τ α, S.hα, by rw [mul_comm, S.hα]⟩
  obtain ⟨g, hg⟩ := exists_UJ σ J (φ.symm ≪≫ₗ (mulUnit A a ≪≫ₗ φ)) (by
    intro u u'
    have h1 := h.mul a (φ.symm u') (φ.symm u)
    have h2 := h (φ.symm u') (φ.symm u)
    rw [show (a : B) = α from rfl, S.hα, mul_one, ← h2] at h1
    simpa using h1)
  exact ⟨g, hg⟩
end HidaSetting
end GlobalTheory.ClassParam
