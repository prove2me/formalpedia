-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:30:03.118933+00:00
-- url     : https://prove2.me/submissions/54411274-a128-4661-8cef-fd3d8bfc590a

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
theorem h44b_norm {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    FiniteEntropy.entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * FiniteEntropy.entropy s (fun a => p a / ∑ b ∈ s, p b) := by
  set S := ∑ a ∈ s, p a with hS
  unfold FiniteEntropy.entropy
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

theorem h44b_eqsum {α : Type*} {β : Type*} {γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    FiniteEntropy.conditionalEntropy s p f g = ∑ c ∈ s.image g, FiniteEntropy.mass s p g c *
      FiniteEntropy.observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / FiniteEntropy.mass s p g c) f := by
  classical
  unfold FiniteEntropy.conditionalEntropy FiniteEntropy.observableEntropy
  -- FiniteEntropy.mass of a pair in terms of the fibre
  have hm2 : ∀ b c, FiniteEntropy.mass s p (fun a => (f a, g a)) (b, c) =
      FiniteEntropy.mass (s.filter (fun a => g a = c)) p f b := by
    intro b c; unfold FiniteEntropy.mass; rw [Finset.filter_filter]
    congr 1; ext a; simp only [Finset.mem_filter, Prod.mk.injEq]; tauto
  -- regroup the pair FiniteEntropy.entropy by the second coordinate
  have hreg : FiniteEntropy.entropy (s.image fun a => (f a, g a)) (FiniteEntropy.mass s p fun a => (f a, g a)) =
      ∑ c ∈ s.image g, FiniteEntropy.entropy ((s.filter (fun a => g a = c)).image f)
        (FiniteEntropy.mass (s.filter (fun a => g a = c)) p f) := by
    unfold FiniteEntropy.entropy
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
  unfold FiniteEntropy.entropy
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  set F := s.filter (fun a => g a = c) with hF
  have hsum : ∑ b ∈ F.image f, FiniteEntropy.mass F p f b = FiniteEntropy.mass s p g c := by
    rw [FiniteEntropy.mass_sum]; rfl
  have hnn : ∀ b ∈ F.image f, 0 ≤ FiniteEntropy.mass F p f b :=
    fun b _ => FiniteEntropy.mass_nonneg F p f (fun a ha => hp a (Finset.mem_filter.mp ha).1) b
  have h := h44b_norm (F.image f) (FiniteEntropy.mass F p f) hnn
  unfold FiniteEntropy.entropy at h
  rw [h, hsum]
  have e : ∀ b ∈ F.image f, FiniteEntropy.mass F p f b / FiniteEntropy.mass s p g c = FiniteEntropy.mass F (fun a => p a / FiniteEntropy.mass s p g c) f b := by
    intro b _; unfold FiniteEntropy.mass; rw [Finset.sum_div]
  rw [Finset.sum_congr rfl fun b hb => by simp only []; rw [e b hb]]
  ring

theorem h44b_logcard {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    FiniteEntropy.entropy s p ≤ Real.log s.card := by
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hs; simp at hs
    · exact h
  have hn : (0:ℝ) < s.card := by exact_mod_cast hne.card_pos
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => (s.card:ℝ)⁻¹) (p := p)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one] at hJ
  unfold FiniteEntropy.entropy
  have e : Real.negMulLog (s.card:ℝ)⁻¹ = (s.card:ℝ)⁻¹ * Real.log s.card := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [e] at hJ
  have := mul_le_mul_of_nonneg_left hJ hn.le
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, one_mul] at this

theorem h44_badmass {α : Type*} {β : Type*} {γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    FiniteEntropy.conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by
  classical
  rw [h44b_eqsum s p f g hp]
  have hq := FiniteEntropy.sum_mass_mul s (s.image g) p g (fun c => if bad c then (1:ℝ) else 0)
    (fun a ha => Finset.mem_image_of_mem g ha)
  have hr : (∑ a ∈ s, if bad (g a) then p a else 0) =
      ∑ c ∈ s.image g, (if bad c then FiniteEntropy.mass s p g c else 0) := by
    simp only [mul_ite, mul_one, mul_zero] at hq; rw [hq]
  rw [hr, Finset.sum_mul]
  have hN : 0 ≤ Real.log (s.image f).card := Real.log_natCast_nonneg _
  refine Finset.sum_le_sum fun c _ => ?_
  set F := s.filter (fun a => g a = c) with hF
  have hm0 : 0 ≤ FiniteEntropy.mass s p g c := FiniteEntropy.mass_nonneg s p g hp c
  rcases hm0.eq_or_lt with h0 | h0
  · rw [← h0, zero_mul]; split_ifs <;> simp
  · have hFsum : ∑ b ∈ F.image f, FiniteEntropy.mass F (fun a => p a / FiniteEntropy.mass s p g c) f b = 1 := by
      rw [FiniteEntropy.mass_sum, ← Finset.sum_div]; exact div_self h0.ne'
    have hH := h44b_logcard (F.image f) (FiniteEntropy.mass F (fun a => p a / FiniteEntropy.mass s p g c) f)
      (fun b _ => FiniteEntropy.mass_nonneg F _ f (fun a ha => div_nonneg (hp a (Finset.mem_filter.mp ha).1) h0.le) b) hFsum
    have hH' : FiniteEntropy.observableEntropy F (fun a => p a / FiniteEntropy.mass s p g c) f ≤ Real.log (F.image f).card := hH
    have hsub : (F.image f).card ≤ (s.image f).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    split_ifs with hb
    · refine mul_le_mul_of_nonneg_left (hH'.trans ?_) h0.le
      apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero (fun h => by
          rw [Finset.card_eq_zero, Finset.image_eq_empty] at h
          have : FiniteEntropy.mass s p g c = 0 := by unfold FiniteEntropy.mass; rw [← hF, h]; simp
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

theorem h44_masscomp {α : Type*} {β : Type*} {γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by
  classical
  simp only [FiniteEntropy.mass, mass, Measure.real_def]
  rw [← ENNReal.toReal_sum (fun b _ => measure_ne_top _ _)]
  congr 1
  have h := sum_measure_preimage_singleton (μ := μ) (s.filter fun b => g b = c)
    (fun y _ => hf (measurableSet_singleton y))
  change _ = ∑ b ∈ s.filter (fun b => g b = c), μ (f ⁻¹' {b})
  rw [h]
  apply measure_congr
  filter_upwards [hs] with x hx
  apply propext
  change g (f x) = c ↔ f x ∈ (s.filter fun b => g b = c)
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

theorem h44_mentfin {α : Type*} {β : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → β)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = FiniteEntropy.entropy s (mass μ f) := by
  unfold entropy FiniteEntropy.entropy
  exact tsum_eq_sum (fun b hb => by rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero])

theorem h44_mentcomp {α : Type*} {β : Type*} {γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  have hs' : ∀ᵐ x ∂μ, (g ∘ f) x ∈ s.image g := hs.mono fun x hx => Finset.mem_image_of_mem g hx
  rw [h44_mentfin μ _ _ hs']
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro c _
  rw [h44_masscomp μ f hf s hs g c]

theorem h44_nml_sum {ι : Type*} (t : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ t, 0 ≤ x i) :
    Real.negMulLog (∑ i ∈ t, x i) ≤ ∑ i ∈ t, Real.negMulLog (x i) := by
  have e : Real.negMulLog (∑ i ∈ t, x i) = ∑ i ∈ t, -x i * Real.log (∑ j ∈ t, x j) := by
    rw [Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    simp only [neg_mul]
  rw [e]
  apply Finset.sum_le_sum
  intro i hi
  rcases (hx i hi).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [Real.negMulLog]
    have : Real.log (x i) ≤ Real.log (∑ j ∈ t, x j) :=
      Real.log_le_log h (Finset.single_le_sum hx hi)
    nlinarith

theorem h44_fdp {α : Type*} {γ : Type*} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (g : α → γ) :
    FiniteEntropy.observableEntropy s p g ≤ FiniteEntropy.entropy s p := by
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy FiniteEntropy.mass
  calc ∑ c ∈ s.image g, Real.negMulLog (∑ a ∈ s.filter (fun a => g a = c), p a)
      ≤ ∑ c ∈ s.image g, ∑ a ∈ s.filter (fun a => g a = c), Real.negMulLog (p a) :=
        Finset.sum_le_sum fun c _ => h44_nml_sum _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem g ha) _

theorem h44_rlmem {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
  unfold relativeLabel label
  have h1 : ((⌊x / t + v⌋ : ℤ) : ℝ) ≤ x / t + v := Int.floor_le _
  have h2 : x / t + v < ((⌊x / t + v⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hts : 0 < t / s := div_pos ht hs
  have e : x / s = t / s * (x / t) := by field_simp
  have h3 : t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v ≤ x / s + u := by
    have := mul_le_mul_of_nonneg_left (show ((⌊x / t + v⌋ : ℤ) : ℝ) - v ≤ x / t by linarith) hts.le
    rw [e]; linarith
  have h4 : x / s + u < t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v + t / s := by
    have := mul_lt_mul_of_pos_left (show x / t < ((⌊x / t + v⌋ : ℤ) : ℝ) + 1 - v by linarith) hts
    rw [e]; linarith
  generalize t / s * ((⌊x / t + v⌋ : ℤ) : ℝ) + u - t / s * v = y at h3 h4 ⊢
  have h5 : ⌊y⌋ ≤ ⌊x / s + u⌋ := Int.floor_le_floor h3
  have h6 : (⌊x / s + u⌋ : ℝ) ≤ x / s + u := Int.floor_le _
  have h7 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h8 : t / s ≤ (⌈t / s⌉ : ℝ) := Int.le_ceil _
  have h9 : ((⌊x / s + u⌋ - ⌊y⌋ : ℤ) : ℝ) < ((⌈t / s⌉ + 1 : ℤ) : ℝ) := by
    push_cast; linarith
  have h10 := Int.cast_lt.mp h9
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (⌈t/s⌉+1 : ℝ) := by
  classical
  obtain ⟨B, hB0, hB⟩ := hμ
  set φ : ℝ → ℤ × ℤ := fun x => (relativeLabel s t u v x, label t v x) with hφdef
  set S : Finset (ℤ × ℤ) := Finset.Icc (0 : ℤ) ⌈t/s⌉ ×ˢ Finset.Icc ⌊-B/t+v⌋ ⌊B/t+v⌋ with hSdef
  have hSa : ∀ᵐ x ∂μ, φ x ∈ S := (label_ae_finite μ ht hB).mono fun x hx =>
    Finset.mem_product.mpr ⟨h44_rlmem hs ht u v x, hx⟩
  have hφm : Measurable φ := by
    have h2 : Measurable (fun x => (label s u x, label t v x)) :=
      (label_measurable s u).prodMk (label_measurable t v)
    have h3 : Measurable (fun r : ℤ × ℤ => (r.1 - ⌊(t/s)*(r.2 : ℝ)+u-(t/s)*v⌋, r.2)) :=
      measurable_of_countable _
    exact h3.comp h2
  set P := mass μ φ with hP
  have hPnn : ∀ a ∈ S, 0 ≤ P a := fun a _ => mass_nonneg μ φ a
  set G : ℤ × ℤ → ℤ := fun r => r.1 + ⌊(t/s)*(r.2 : ℝ)+u-(t/s)*v⌋ with hG
  have hGφ : label s u = G ∘ φ := by
    funext x
    simp only [hG, hφdef, Function.comp_apply, relativeLabel]
    ring
  have h1 : grid μ s u = FiniteEntropy.observableEntropy S P G := by
    unfold grid; rw [hGφ]; exact h44_mentcomp μ φ hφm S hSa G
  have h2 : grid μ t v = FiniteEntropy.observableEntropy S P Prod.snd := by
    unfold grid; exact h44_mentcomp μ φ hφm S hSa Prod.snd
  have h3 : FiniteEntropy.entropy S P =
      FiniteEntropy.observableEntropy S P (fun a => (a.1, a.2)) := by
    rw [← h44_mentfin μ φ S hSa]
    exact h44_mentcomp μ φ hφm S hSa (fun a => (a.1, a.2))
  have hdp := h44_fdp S P hPnn G
  have hc := h44_badmass S P Prod.fst Prod.snd (fun _ => True) hPnn
    (fun a _ b _ _ h => absurd trivial h)
  simp only [if_true] at hc
  rw [mass_sum μ φ hφm S hSa, one_mul] at hc
  unfold FiniteEntropy.conditionalEntropy at hc
  have hts : (0 : ℤ) ≤ ⌈t/s⌉ := Int.ceil_nonneg (div_pos ht hs).le
  have hcard : ((S.image Prod.fst).card : ℤ) ≤ ⌈t/s⌉ + 1 := by
    have himg : S.image Prod.fst ⊆ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      exact (Finset.mem_product.mp ha).1
    have := Finset.card_le_card himg
    rw [Int.card_Icc] at this
    omega
  have hlog : Real.log ((S.image Prod.fst).card : ℝ) ≤ Real.log (⌈t/s⌉+1 : ℝ) := by
    have hR : ((S.image Prod.fst).card : ℝ) ≤ (⌈t/s⌉ : ℝ) + 1 := by exact_mod_cast hcard
    rcases Nat.eq_zero_or_pos (S.image Prod.fst).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (⌈t/s⌉ : ℝ) := by exact_mod_cast hts
      linarith
    · exact Real.log_le_log (by exact_mod_cast h0) hR
  rw [h1, h2]
  linarith

