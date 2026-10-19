-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:28:13.407776+00:00
-- url     : https://prove2.me/submissions/7d9cc5ad-a794-40ed-b1d3-c156b3f686f9

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h43_norm {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * entropy s (fun a => p a / ∑ b ∈ s, p b) := by
  set S := ∑ a ∈ s, p a with hS
  unfold entropy
  rcases eq_or_ne S 0 with h0 | h0
  · have hz : ∀ a ∈ s, p a = 0 := (Finset.sum_eq_zero_iff_of_nonneg hp).mp h0.symm.symm
    rw [h0]; simp only [Real.negMulLog_zero, div_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero fun a ha => by rw [hz a ha, Real.negMulLog_zero]
  · have e : ∀ a ∈ s, Real.negMulLog (p a) =
        (p a / S) * Real.negMulLog S + S * Real.negMulLog (p a / S) := by
      intro a _
      rw [← Real.negMulLog_mul, mul_div_cancel₀ _ h0]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.sum_div, div_self h0, one_mul]

theorem solution {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p f g = ∑ c ∈ s.image g, mass s p g c *
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
  classical
  unfold conditionalEntropy observableEntropy
  -- mass of a pair in terms of the fibre
  have hm2 : ∀ b c, mass s p (fun a => (f a, g a)) (b, c) =
      mass (s.filter (fun a => g a = c)) p f b := by
    intro b c; unfold mass; rw [Finset.filter_filter]
    congr 1; ext a; simp only [Finset.mem_filter, Prod.mk.injEq]; tauto
  -- regroup the pair entropy by the second coordinate
  have hreg : entropy (s.image fun a => (f a, g a)) (mass s p fun a => (f a, g a)) =
      ∑ c ∈ s.image g, entropy ((s.filter (fun a => g a = c)).image f)
        (mass (s.filter (fun a => g a = c)) p f) := by
    unfold entropy
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.snd) (t := s.image g)
      (fun x hx => by
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image_of_mem g ha)]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hset : (s.image fun a => (f a, g a)).filter (fun x => x.2 = c) =
        ((s.filter (fun a => g a = c)).image f).image (fun b => (b, c)) := by
      ext ⟨b, c'⟩
      simp only [Finset.mem_filter, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨a, ha, h1, h2⟩, rfl⟩; exact ⟨b, ⟨a, ⟨ha, h2⟩, h1⟩, rfl, rfl⟩
      · rintro ⟨b', ⟨a, ⟨ha, h2⟩, h1⟩, h3, rfl⟩; exact ⟨⟨a, ha, h1.trans h3, h2⟩, rfl⟩
    rw [hset, Finset.sum_image (fun x _ y _ h => by simpa using h)]
    exact Finset.sum_congr rfl fun b _ => by rw [hm2]
  rw [hreg]
  unfold entropy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  set F := s.filter (fun a => g a = c) with hF
  have hsum : ∑ b ∈ F.image f, mass F p f b = mass s p g c := by
    rw [mass_sum]; rfl
  have hnn : ∀ b ∈ F.image f, 0 ≤ mass F p f b :=
    fun b _ => mass_nonneg F p f (fun a ha => hp a (Finset.mem_filter.mp ha).1) b
  have h := h43_norm (F.image f) (mass F p f) hnn
  unfold entropy at h
  rw [h, hsum]
  have e : ∀ b ∈ F.image f, mass F p f b / mass s p g c = mass F (fun a => p a / mass s p g c) f b := by
    intro b _; unfold mass; rw [Finset.sum_div]
  rw [Finset.sum_congr rfl fun b hb => by simp only []; rw [e b hb]]
  ring

