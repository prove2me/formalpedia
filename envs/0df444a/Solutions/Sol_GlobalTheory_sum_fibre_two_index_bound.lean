-- Prove2me | solution 1 for GlobalTheory.sum_fibre_two_index_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:07.015931+00:00
-- url     : https://prove2.me/submissions/d3e665d3-af79-4722-9467-0f00036108fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumFibreTwoIndexEncardBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc
end GlobalTheory
