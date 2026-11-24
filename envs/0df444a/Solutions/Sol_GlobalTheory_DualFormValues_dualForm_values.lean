-- Prove2me | solution 1 for GlobalTheory.DualFormValues.dualForm_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:56.665275+00:00
-- url     : https://prove2.me/submissions/44f2d3a8-0830-47e9-a0bd-f33bb65c5ae0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RiemannClEqSum
import Theorems.Thm_GlobalTheory_DualFormValues_trace_eq_sum
import Theorems.Thm_GlobalTheory_DualFormValues_coeff_eq_zero
import Theorems.Thm_GlobalTheory_DualFormValues_riemannCl_eq_sum
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DualFormValues
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.DualFormValues
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E) (hξ : ξ ≠ 0)
    (_hc : IsCMField.complexConj E ξ = -ξ) (B : LinearMap.BilinForm ℂ (Coh E)) (hB : IsDualForm ξ B)
    (ρ ρ' : E →+* ℂ) :
    (ρ' = ComplexEmbedding.conjugate ρ →
      B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
    (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0) := by
  classical
  let b : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun a a' => B a.toRatAlgHom.toLinearMap a'.toRatAlgHom.toLinearMap
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ₁ τ₂ =>
    τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) -
      if τ₂ = ComplexEmbedding.conjugate τ₁ then τ₁ ξ else 0
  have hz : ∀ τ : E →+* ℂ, τ ξ ≠ 0 := fun τ => by simpa using hξ
  have hsum : ∀ x y : E, ∑ τ₁, ∑ τ₂, c τ₁ τ₂ * (τ₁ x * τ₂ y) = 0 := by
    intro x y
    have h1 := hB x y
    rw [riemannCl_eq_sum, riemannCl_eq_sum] at h1
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : ((riemann ξ x y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      simp only [riemann, trace_eq_sum, map_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h2] at h1
    simp only [c, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    rw [sub_eq_zero]
    have h3 : ∑ τ₁, ∑ τ₂, τ₁ ξ * τ₂ ξ * b (ComplexEmbedding.conjugate τ₁) (ComplexEmbedding.conjugate τ₂) *
        (τ₁ x * τ₂ y) = ∑ σ : E →+* ℂ, σ ξ * σ x * ComplexEmbedding.conjugate σ y := by
      rw [← h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun τ₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ₁ _ => ?_
      simp only [b, map_mul]
      ring
    rw [h3]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hc := coeff_eq_zero c hsum (ComplexEmbedding.conjugate ρ) (ComplexEmbedding.conjugate ρ')
  simp only [c, b, hcc] at hc
  constructor
  · rintro rfl
    rw [hcc, if_pos rfl] at hc
    have h0 := hz (ComplexEmbedding.conjugate ρ)
    have h4 : ComplexEmbedding.conjugate ρ ξ *
        (ρ ξ * B ρ.toRatAlgHom.toLinearMap (ComplexEmbedding.conjugate ρ).toRatAlgHom.toLinearMap - 1) = 0 := by
      linear_combination hc
    have h5 := (mul_eq_zero.1 h4).resolve_left h0
    exact eq_inv_of_mul_eq_one_right (sub_eq_zero.1 h5)
  · intro hne
    have hne' : ComplexEmbedding.conjugate ρ' ≠ ρ := fun h => hne (by rw [← h, hcc])
    rw [if_neg hne', sub_zero] at hc
    exact (mul_eq_zero.1 hc).resolve_left (mul_ne_zero (hz _) (hz _))
end GlobalTheory.DualFormValues
