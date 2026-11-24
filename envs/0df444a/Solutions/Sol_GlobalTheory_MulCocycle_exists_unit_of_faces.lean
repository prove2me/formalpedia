-- Prove2me | solution 1 for GlobalTheory.MulCocycle.exists_unit_of_faces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:22.075095+00:00
-- url     : https://prove2.me/submissions/824dc06e-f6c4-4f48-b17b-feb1e06ed216

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
import Theorems.Thm_GlobalTheory_MulCocycle_algHom_mem_map
import Theorems.Thm_GlobalTheory_MulCocycle_mul_mem_map_sq
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle
variable {B : Type*} [CommRing B] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
namespace GlobalTheory.MulCocycle
theorem _root_.solution {R₁ R₂ R₃ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [Algebra B R₁] [Algebra B R₂] [Algebra B R₃]
    (e₀ e₁ e₂ : R₁ →ₐ[B] R₂) (d₀ d₁ d₂ d₃ : R₂ →ₐ[B] R₃)
    (h₁ : ∀ w, d₁ (e₁ w) = d₂ (e₁ w)) (h₂ : ∀ w, d₁ (e₂ w) = d₃ (e₁ w))
    (h₃ : ∀ w, d₁ (e₀ w) = d₀ (e₀ w)) (h₄ : ∀ w, d₃ (e₂ w) = d₂ (e₂ w))
    (h₅ : ∀ w, d₃ (e₀ w) = d₀ (e₂ w)) (h₆ : ∀ w, d₂ (e₀ w) = d₀ (e₁ w))
    (H : ∀ (K L : Ideal B) (φ : R₂), φ ∈ K.map (algebraMap B R₂) →
      d₀ φ - d₁ φ + d₂ φ - d₃ φ ∈ L.map (algebraMap B R₃) →
      ∃ ψ ∈ K.map (algebraMap B R₁), φ - (e₀ ψ - e₁ ψ + e₂ ψ) ∈ L.map (algebraMap B R₂))
    (n : ℕ) : ∀ (K : Ideal B), K ^ 2 ^ n = ⊥ → ∀ f : R₂, f - 1 ∈ K.map (algebraMap B R₂) →
      d₁ f * d₃ f = d₂ f * d₀ f →
      ∃ g : R₁ˣ, g.val - 1 ∈ K.map (algebraMap B R₁) ∧ f * e₁ g.val = e₂ g.val * e₀ g.val := by
  induction n with
  | zero =>
    intro K hK f hf _
    rw [pow_zero, pow_one] at hK
    rw [hK, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at hf
    exact ⟨1, by simp, by simp [hf]⟩
  | succ n ih =>
    intro K hK f hf hc
    obtain ⟨φ, rfl⟩ : ∃ φ, f = 1 + φ := ⟨f - 1, by ring⟩
    rw [add_sub_cancel_left] at hf
    have hc' := hc
    simp only [map_add, map_one] at hc'
    obtain ⟨ψ, hψ, e⟩ := H K (K ^ 2) φ hf (by
      have : d₀ φ - d₁ φ + d₂ φ - d₃ φ = d₁ φ * d₃ φ - d₂ φ * d₀ φ := by
        linear_combination -hc'
      rw [this]
      exact sub_mem (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf))
        (mul_mem_map_sq (algHom_mem_map _ hf) (algHom_mem_map _ hf)))
    have hn : IsNilpotent ψ := ⟨2 ^ (n + 1), by
      have := Ideal.pow_mem_pow hψ (2 ^ (n + 1))
      rwa [← Ideal.map_pow, hK, Ideal.map_bot, Ideal.mem_bot] at this⟩
    obtain ⟨u, hu⟩ := hn.isUnit_one_add
    have huv : u.val * (u⁻¹).val = 1 := u.mul_inv
    generalize (u⁻¹).val = v at huv
    have k (e : R₁ →ₐ[B] R₂) : e u.val * e v = 1 := by rw [← map_mul, huv, map_one]
    have k' (d : R₂ →ₐ[B] R₃) (e : R₁ →ₐ[B] R₂) : d (e u.val) * d (e v) = 1 := by
      rw [← map_mul, k, map_one]
    obtain ⟨g, hg, hg'⟩ := ih (K ^ 2) (by rw [← pow_mul, ← pow_succ', hK])
      ((1 + φ) * e₁ u.val * e₂ v * e₀ v) (by
        have : (1 + φ) * e₁ u.val * e₂ v * e₀ v - 1 =
            ((φ - (e₀ ψ - e₁ ψ + e₂ ψ)) + φ * e₁ ψ - e₂ ψ * e₀ ψ) * (e₂ v * e₀ v) := by
          have k₀ := k e₀
          have k₂ := k e₂
          rw [hu] at k₀ k₂ ⊢
          simp only [map_add, map_one] at k₀ k₂ ⊢
          linear_combination ((1 + e₀ ψ) * e₀ v) * k₂ + k₀
        rw [this]
        exact Ideal.mul_mem_right _ _ (sub_mem (add_mem e
          (mul_mem_map_sq hf (algHom_mem_map _ hψ)))
          (mul_mem_map_sq (algHom_mem_map _ hψ) (algHom_mem_map _ hψ)))) (by
        have k₁ := k' d₃ e₁
        have k₂ := k' d₀ e₁
        generalize 1 + φ = f at hc
        simp only [map_mul, h₁, h₂, h₃, h₄, h₅, h₆]
        linear_combination
          (d₂ (e₁ u.val) * d₂ (e₂ v) * d₀ (e₂ v) * d₀ (e₀ v)) *
            (d₁ f * d₃ f * k₁ - d₂ f * d₀ f * k₂ + hc))
    refine ⟨u * g, ?_, ?_⟩
    · have : (u * g).val - 1 = u.val * (g.val - 1) + ψ := by
        rw [Units.val_mul, hu]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _
        (Ideal.map_mono (Ideal.pow_le_self two_ne_zero) hg)) hψ
    · have k₀ := k e₀
      have k₂ := k e₂
      simp only [Units.val_mul, map_mul]
      linear_combination (e₂ u.val * e₀ u.val) * hg' -
        ((1 + φ) * e₁ u.val * e₁ g.val) * (e₀ u.val * e₀ v * k₂ + k₀)
end GlobalTheory.MulCocycle
