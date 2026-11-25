-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.exists_extend_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:43:52.627178+00:00
-- url     : https://prove2.me/submissions/5b868dc2-d478-47d8-b22b-8f2e4444b0a0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isOrthoCompl_orthogonal
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_extend_of_isOrthoCompl
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
    (h : HermitianForm F E V) {U₁ U₂ : Submodule E V}
    (hU : ∀ u ∈ U₁, (∀ u' ∈ U₁, h.toSesq u u' = 0) → u = 0) (φ : U₁ ≃ₗ[E] U₂)
    (hφ : ∀ x y : U₁, h.toSesq (φ x) (φ y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U₁, g x = φ x := by
  have hU₂ : ∀ u ∈ U₂, (∀ u' ∈ U₂, h.toSesq u u' = 0) → u = 0 := by
    intro u hu H
    have h1 : ((φ.symm ⟨u, hu⟩ : U₁) : V) = 0 := by
      apply hU _ (φ.symm ⟨u, hu⟩).2
      intro u' hu'
      rw [← hφ (φ.symm ⟨u, hu⟩) ⟨u', hu'⟩, LinearEquiv.apply_symm_apply]
      exact H _ (φ ⟨u', hu'⟩).2
    have h2 : φ.symm ⟨u, hu⟩ = 0 := Subtype.ext h1
    have h3 : (⟨u, hu⟩ : U₂) = 0 := by rw [← φ.apply_symm_apply ⟨u, hu⟩, h2, map_zero]
    exact congrArg Subtype.val h3
  exact h.exists_extend_of_isOrthoCompl (h.isOrthoCompl_orthogonal U₁ hU)
    (h.isOrthoCompl_orthogonal U₂ hU₂) φ hφ
end GroundTheory.Automorphic.HermitianForm
