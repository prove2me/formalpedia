-- Prove2me | solution 1 for GlobalTheory.ClassParam.HidaSetting.norm_of_isConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:47:11.871785+00:00
-- url     : https://prove2.me/submissions/766af3bd-5624-4453-9be5-6e11710384dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_mem_UJ_iff
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_eq_of_trace
import Theorems.Thm_GlobalTheory_ClassParam_HidaSetting_map_mul_of_comm

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
theorem _root_.solution (S : HidaSetting σ τ α b) {x x' : B} {φ φ' : B ≃ₗ[A] (Fin r → A)}
    (h : Iso σ τ J x φ) (h' : Iso σ τ J x' φ') {g g' : UJ σ J}
    (hg : Intw α ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ)
    (hg' : Intw α ((g' : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) φ') (hc : IsConj g' g) :
    ∃ z : Bˣ, x' = x * (z * τ z) := by
  obtain ⟨t, ht⟩ := isConj_iff.1 hc
  rw [mul_inv_eq_iff_eq_mul] at ht
  have ht' : ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (g' : GL (Fin r) A)
      = ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * (t : GL (Fin r) A) :=
    congrArg (fun s : UJ σ J => ((s : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) ht
  let T : (Fin r → A) ≃ₗ[A] (Fin r → A) := Matrix.toLinearEquiv' ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)
    (Units.invertible _)
  have hT : ∀ u, T u = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u := fun u => rfl
  let ψ : B ≃ₗ[A] B := φ' ≪≫ₗ T ≪≫ₗ φ.symm
  have hψ : ∀ y, φ (ψ y) = ((t : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ φ' y := fun y => by
    simp [ψ, hT]
  have hcomm : ∀ y, ψ (α * y) = α * ψ y := by
    intro y
    apply φ.injective
    have e1 := hg' (φ' y)
    have e2 := hg (φ (ψ y))
    rw [LinearEquiv.symm_apply_apply] at e1 e2
    rw [hψ, ← e1, ← e2, hψ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ht']
  have hm : ∀ y, ψ y = ψ 1 * y := S.map_mul_of_comm ψ.toLinearMap hcomm
  have hu : IsUnit (ψ 1) := IsUnit.of_mul_eq_one (ψ.symm 1) (by rw [← hm]; simp)
  refine ⟨hu.unit, S.eq_of_trace fun y => ?_⟩
  have e1 := h' y 1
  have e2 := h (ψ y) (ψ 1)
  rw [hψ, hψ, (mem_UJ_iff σ J _).1 t.2, e1, hm y] at e2
  unfold tf at e2
  rw [map_one, mul_one] at e2
  rw [e2, IsUnit.unit_spec]
  congr 1; ring
end HidaSetting
end GlobalTheory.ClassParam
