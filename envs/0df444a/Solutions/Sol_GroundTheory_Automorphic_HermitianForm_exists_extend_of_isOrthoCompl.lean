-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_extend_of_isOrthoCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:35:56.994299+00:00
-- url     : https://prove2.me/submissions/96cafc05-a28d-4f0b-8a99-61432b905d2b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_of_prod_isometric_prod
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_prodEquivOfIsCompl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_refl
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_comm
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_restrict
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {U₁ U₁' U₂ U₂' : Submodule E V} (h1 : h.IsOrthoCompl U₁ U₁')
    (h2 : h.IsOrthoCompl U₂ U₂') (φ : U₁ ≃ₗ[E] U₂)
    (hφ : ∀ x y : U₁, h.toSesq (φ x) (φ y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U₁, g x = φ x := by
  have I1 := h.isometric_prod_restrict U₁ U₁' h1
  have I2 := h.isometric_prod_restrict U₂ U₂' h2
  have Iφ : Isometric (h.restrict U₁ U₁' h1) (h.restrict U₂ U₂' h2) := ⟨φ, hφ⟩
  have I3 : Isometric ((h.restrict U₁' U₁ h1.symm).prod (h.restrict U₂ U₂' h2))
      ((h.restrict U₂' U₂ h2.symm).prod (h.restrict U₂ U₂' h2)) :=
    (((Isometric.refl _).prod Iφ.symm).trans (isometric_prod_comm _ _)).trans
      (I1.trans (I2.symm.trans (isometric_prod_comm _ _)))
  obtain ⟨ψ, hψ⟩ := isometric_of_prod_isometric_prod _ _ _ I3
  have hψ' : ∀ a b : U₁', h.toSesq (ψ a : V) (ψ b) = h.toSesq a b := fun a b => hψ a b
  set e₁ := Submodule.prodEquivOfIsCompl U₁ U₁' h1.1
  set e₂ := Submodule.prodEquivOfIsCompl U₂ U₂' h2.1
  refine ⟨(e₁.symm.trans (φ.prodCongr ψ)).trans e₂, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨p, rfl⟩ := e₁.surjective x
    obtain ⟨q, rfl⟩ := e₁.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply]
    rw [toSesq_prodEquivOfIsCompl h h2, toSesq_prodEquivOfIsCompl h h1, hφ, hψ']
  · simp only [LinearEquiv.trans_apply, e₁, e₂, Submodule.prodEquivOfIsCompl_symm_apply_left,
      LinearEquiv.prodCongr_apply, map_zero, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_zero, add_zero]
end GroundTheory.Automorphic.HermitianForm
