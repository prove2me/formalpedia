-- Prove2me | solution 1 for GroundTheory.Automorphic.HermitianForm.stableInv_eq_stableInv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:46.146261+00:00
-- url     : https://prove2.me/submissions/447a512b-6a93-47b0-a4c3-84aac00d5f67

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mul_inv_mem_unitaryGroup
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_normOf_eq_of_adjoint
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_invOf_eq_of_eq
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_stableInv_conj
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_inv
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mem
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mk
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mul
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_one
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.TorusE.val_inv
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mk
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mul
attribute [local simp] GroundTheory.Automorphic.TorusE.val_one
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
namespace GroundTheory.Automorphic.HermitianForm
theorem _root_.solution {γ₁ γ₂ : V ≃ₗ[E] V} (h₁ : γ₁ ∈ h.unitaryGroup)
    (h₂ : γ₂ ∈ h.unitaryGroup) (s₁ : StablyConjugate (γ : V ≃ₗ[E] V) γ₁)
    (s₂ : StablyConjugate (γ : V ≃ₗ[E] V) γ₂) :
    h.stableInv γ γ₁ = h.stableInv γ γ₂ ↔ ∃ u ∈ h.unitaryGroup, u * γ₁ * u⁻¹ = γ₂ := by
  obtain ⟨g₁, rfl⟩ := s₁
  obtain ⟨g₂, rfl⟩ := s₂
  rw [stableInv_conj _ _ _ h₁, stableInv_conj _ _ _ h₂]
  constructor
  · intro heq
    rw [invOf, invOf, mk_eq_mk_iff] at heq
    obtain ⟨t, ht⟩ := heq
    have htγ := mem_torusE.1 t.val_mem
    set a := g₁ * t.val with ha
    have hc : (h.normOf γ g₁ h₁ : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
        h.torusStar γ t * h.normOf γ g₁ h₁ * t := by
      rw [torusNorm_apply]
      simp only [mul_comm, mul_left_comm]
    have key : h.adjointEquiv a * a = h.adjointEquiv g₂ * g₂ := by
      have := congrArg TorusE.val (ht.trans hc)
      simp only [TorusE.val_mul, val_torusStar, val_normOf] at this
      rw [this, ha, adjointEquiv_mul]
      group
    refine ⟨g₂ * a⁻¹, h.mul_inv_mem_unitaryGroup key, ?_⟩
    calc g₂ * a⁻¹ * (g₁ * γ * g₁⁻¹) * (g₂ * a⁻¹)⁻¹
        = g₂ * t.val⁻¹ * (γ * t.val) * g₂⁻¹ := by simp only [a]; group
      _ = g₂ * t.val⁻¹ * (t.val * γ) * g₂⁻¹ := by rw [htγ]
      _ = g₂ * γ * g₂⁻¹ := by group
  · rintro ⟨u, hu, hu'⟩
    have hug : (u * g₁) * γ * (u * g₁)⁻¹ = g₂ * γ * g₂⁻¹ := by
      rw [← hu']; group
    have hug' : (u * g₁) * γ * (u * g₁)⁻¹ ∈ h.unitaryGroup := by rw [hug]; exact h₂
    rw [← h.invOf_eq_of_eq γ _ _ hug' h₂ hug, invOf, invOf,
      h.normOf_eq_of_adjoint γ (u * g₁) g₁ hug' h₁]
    rw [adjointEquiv_mul, (h.mem_unitaryGroup_iff_adjointEquiv u).1 hu]
    group
end GroundTheory.Automorphic.HermitianForm
