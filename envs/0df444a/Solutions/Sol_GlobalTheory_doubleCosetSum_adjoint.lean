-- Prove2me | solution 1 for GlobalTheory.doubleCosetSum_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:17.42683+00:00
-- url     : https://prove2.me/submissions/355d8f11-4f26-4d91-8128-8223a514bdae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetSumFundamentalDomain
import Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_setIntegral_mul_right
import Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_integrableOn_mul_right
import Theorems.Thm_GlobalTheory_DoubleCosetAdjoint_integrableOn_star_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.DoubleCosetAdjoint
namespace GlobalTheory
theorem _root_.solution : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (Γ K : Subgroup H) [Countable Γ] (𝓕 : Set H) (x : H) (A A' : Finset H) (F F' : H → ℂ), IsFundamentalDomain Γ 𝓕 μ → (∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂) → (∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) → A.card = A'.card → Continuous F → Continuous F' → (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) → (∀ γ ∈ Γ, ∀ h, F' (γ * h) = F' h) → (∀ k ∈ K, ∀ h, F (h * k) = F h) → (∀ k ∈ K, ∀ h, F' (h * k) = F' h) → IntegrableOn (fun h => star (F h) * F h) 𝓕 μ → IntegrableOn (fun h => star (F' h) * F' h) 𝓕 μ → ∫ h in 𝓕, star (∑ a ∈ A, F (h * a)) * F' h ∂μ = ∫ h in 𝓕, star (F h) * ∑ a ∈ A', F' (h * a) ∂μ := by
  intro H _ _ _ _ _ μ _ _ Γ K _ 𝓕 x A A' F F' h𝓕 hA hA' hc cF cF' lF lF' rF rF' iF iF'
  set u : H → ℂ := fun h => star (F (h * x)) * F' h with hu
  have lu : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h := by
    intro γ hγ h
    simp only [hu, mul_assoc, lF γ hγ, lF' γ hγ]
  have iu : IntegrableOn u 𝓕 μ := by
    refine integrableOn_star_mul μ 𝓕 (fun h => F (h * x)) F'
      (cF.comp (continuous_mul_right x)) cF' ?_ iF'
    exact integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h)
      (fun γ hγ h => by simp only [lF γ hγ]) x iF
  have eA : ∀ a ∈ A, ∃ y, ∀ h, star (F (h * a)) * F' h = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF k₂ hk₂, rF' k₁ hk₁]
  have eA' : ∀ a ∈ A', ∃ y, ∀ h, star (F h) * F' (h * a) = u (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, fun h => ?_⟩
    simp only [hu, ← mul_assoc, rF' k₂ hk₂, inv_mul_cancel_right, rF k₁ hk₁]
  have key : ∀ (B : Finset H) (t : H → H → ℂ), (∀ a ∈ B, ∃ y, ∀ h, t a h = u (h * y)) →
      ∫ h in 𝓕, ∑ a ∈ B, t a h ∂μ = B.card • ∫ h in 𝓕, u h ∂μ := by
    intro B t ht
    rw [integral_finset_sum, ← Finset.sum_const]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨y, hy⟩ := ht a ha
      simp only [hy]
      exact setIntegral_mul_right μ Γ 𝓕 h𝓕 u lu y
    · intro a ha
      obtain ⟨y, hy⟩ := ht a ha
      have : t a = fun h => u (h * y) := funext hy
      rw [this]
      exact integrableOn_mul_right μ Γ 𝓕 h𝓕 u lu y iu
  simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
  rw [key A (fun a h => star (F (h * a)) * F' h) eA,
    key A' (fun a h => star (F h) * F' (h * a)) eA', hc]
end GlobalTheory
