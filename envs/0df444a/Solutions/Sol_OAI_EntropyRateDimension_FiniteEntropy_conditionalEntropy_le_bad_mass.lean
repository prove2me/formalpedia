-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:29:44.173658+00:00
-- url     : https://prove2.me/submissions/334dbfd6-856a-4a8d-bd24-a5274efd07c1

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

theorem h43_eqsum {α : Type*} {β : Type*} {γ : Type*} [DecidableEq β] [DecidableEq γ]
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

theorem h43_logcard {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    entropy s p ≤ Real.log s.card := by
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hs; simp at hs
    · exact h
  have hn : (0:ℝ) < s.card := by exact_mod_cast hne.card_pos
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => (s.card:ℝ)⁻¹) (p := p)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one] at hJ
  unfold entropy
  have e : Real.negMulLog (s.card:ℝ)⁻¹ = (s.card:ℝ)⁻¹ * Real.log s.card := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [e] at hJ
  have := mul_le_mul_of_nonneg_left hJ hn.le
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, one_mul] at this

theorem solution {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by
  classical
  rw [h43_eqsum s p f g hp]
  have hq := sum_mass_mul s (s.image g) p g (fun c => if bad c then (1:ℝ) else 0)
    (fun a ha => Finset.mem_image_of_mem g ha)
  have hr : (∑ a ∈ s, if bad (g a) then p a else 0) =
      ∑ c ∈ s.image g, (if bad c then mass s p g c else 0) := by
    simp only [mul_ite, mul_one, mul_zero] at hq; rw [hq]
  rw [hr, Finset.sum_mul]
  have hN : 0 ≤ Real.log (s.image f).card := Real.log_natCast_nonneg _
  refine Finset.sum_le_sum fun c _ => ?_
  set F := s.filter (fun a => g a = c) with hF
  have hm0 : 0 ≤ mass s p g c := mass_nonneg s p g hp c
  rcases hm0.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; split_ifs <;> simp
  · have hFsum : ∑ b ∈ F.image f, mass F (fun a => p a / mass s p g c) f b = 1 := by
      rw [mass_sum, ← Finset.sum_div]; exact div_self h0.ne'
    have hH := h43_logcard (F.image f) (mass F (fun a => p a / mass s p g c) f)
      (fun b _ => mass_nonneg F _ f (fun a ha => div_nonneg (hp a (Finset.mem_filter.mp ha).1) h0.le) b) hFsum
    have hH' : observableEntropy F (fun a => p a / mass s p g c) f ≤ Real.log (F.image f).card := hH
    have hsub : (F.image f).card ≤ (s.image f).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    split_ifs with hb
    · refine mul_le_mul_of_nonneg_left (hH'.trans ?_) h0.le
      apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero (fun h => by
          rw [Finset.card_eq_zero, Finset.image_eq_empty] at h
          have : mass s p g c = 0 := by unfold mass; rw [← hF, h]; simp
          linarith)
      · exact_mod_cast hsub
    · have h1 : (F.image f).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hy
        rw [hF, Finset.mem_filter] at ha hb'
        exact hgood a ha.1 b hb'.1 (ha.2.trans hb'.2.symm) (by rw [ha.2]; exact hb)
      have hl : Real.log (F.image f).card ≤ 0 := by
        interval_cases h : (F.image f).card <;> simp
      rw [zero_mul]; nlinarith

