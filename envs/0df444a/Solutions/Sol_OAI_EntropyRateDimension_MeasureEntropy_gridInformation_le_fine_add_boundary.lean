-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.gridInformation_le_fine_add_boundary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:11:56.715761+00:00
-- url     : https://prove2.me/submissions/d9d68856-e05e-49b3-80c6-3247c1bfa5f8

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable
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

theorem h44_lsum {ι : Type*} (t : Finset ι) (a A : ι → ℝ) (ha : ∀ i ∈ t, 0 ≤ a i)
    (haA : ∀ i ∈ t, a i ≤ A i) :
    (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / (∑ i ∈ t, A i)) ≤
      ∑ i ∈ t, a i * Real.log (a i / A i) := by
  have hA0 : ∀ i ∈ t, 0 ≤ A i := fun i hi => (ha i hi).trans (haA i hi)
  set S := ∑ i ∈ t, A i with hS
  rcases (Finset.sum_nonneg hA0).eq_or_lt with h0 | hpos
  · have hz : ∀ i ∈ t, A i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hA0).mp h0.symm
    have hz' : ∀ i ∈ t, a i = 0 := fun i hi => le_antisymm (hz i hi ▸ haA i hi) (ha i hi)
    rw [Finset.sum_eq_zero hz', zero_mul]
    exact le_of_eq (Finset.sum_eq_zero (fun i hi => by rw [hz' i hi, zero_mul])).symm
  · have hJ := Real.convexOn_mul_log.map_sum_le (t := t) (w := fun i => A i / S)
      (p := fun i => a i / A i)
      (fun i hi => div_nonneg (hA0 i hi) hpos.le) (by rw [← Finset.sum_div]; exact div_self hpos.ne')
      (fun i hi => Set.mem_Ici.mpr (div_nonneg (ha i hi) (hA0 i hi)))
    simp only [smul_eq_mul] at hJ
    have e1 : ∑ i ∈ t, A i / S * (a i / A i) = (∑ i ∈ t, a i) / S := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rcases (hA0 i hi).eq_or_lt with h | h
      · have : a i = 0 := le_antisymm (h ▸ haA i hi) (ha i hi)
        rw [← h, this]; simp
      · field_simp
    have e2 : ∀ i ∈ t, A i / S * (a i / A i * Real.log (a i / A i)) =
        (a i * Real.log (a i / A i)) / S := by
      intro i hi
      rcases (hA0 i hi).eq_or_lt with h | h
      · have : a i = 0 := le_antisymm (h ▸ haA i hi) (ha i hi)
        rw [← h, this]; simp
      · field_simp
    rw [e1, Finset.sum_congr rfl e2, ← Finset.sum_div] at hJ
    have := mul_le_mul_of_nonneg_left hJ hpos.le
    rwa [mul_div_cancel₀ _ hpos.ne', ← mul_assoc, mul_div_cancel₀ _ hpos.ne'] at this

theorem h44_Dform {α γ : Type*} [DecidableEq γ] (J : Finset α) (h : α → γ) (p : α → ℝ) (hp : ∀ j ∈ J, 0 ≤ p j) :
    FiniteEntropy.entropy J p - FiniteEntropy.observableEntropy J p h =
      -∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        p j * Real.log (p j / FiniteEntropy.mass J p h c) := by
  unfold FiniteEntropy.observableEntropy
  unfold FiniteEntropy.entropy
  rw [← Finset.sum_fiberwise_of_maps_to (g := h) (t := J.image h)
    (fun j hj => Finset.mem_image_of_mem h hj) (fun j => Real.negMulLog (p j))]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro c _
  have hM : FiniteEntropy.mass J p h c = ∑ j ∈ J.filter (fun j => h j = c), p j := rfl
  have e : Real.negMulLog (FiniteEntropy.mass J p h c) =
      ∑ j ∈ J.filter (fun j => h j = c), -(p j) * Real.log (FiniteEntropy.mass J p h c) := by
    rw [hM, Real.negMulLog, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hpj := hp j (Finset.mem_filter.mp hj).1
  rcases hpj.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have hMpos : 0 < FiniteEntropy.mass J p h c := by
      rw [hM]
      exact lt_of_lt_of_le hpos (Finset.single_le_sum
        (fun k hk => hp k (Finset.mem_filter.mp hk).1) hj)
    rw [Real.negMulLog, Real.log_div hpos.ne' hMpos.ne']
    ring

theorem h44_conc {ι α γ : Type*} [Fintype ι] [DecidableEq γ] (J : Finset α) (h : α → γ) (p : ι → α → ℝ)
    (hp : ∀ i, ∀ j ∈ J, 0 ≤ p i j) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        (∑ i, w i * p i j) * Real.log ((∑ i, w i * p i j) /
          FiniteEntropy.mass J (fun k => ∑ i, w i * p i k) h c) ≤
      ∑ i, w i * ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        p i j * Real.log (p i j / FiniteEntropy.mass J (p i) h c) := by
  have hmass : ∀ c, FiniteEntropy.mass J (fun k => ∑ i, w i * p i k) h c =
      ∑ i, w i * FiniteEntropy.mass J (p i) h c := by
    intro c
    unfold FiniteEntropy.mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc _ ≤ ∑ c ∈ J.image h, ∑ j ∈ J.filter (fun j => h j = c),
        ∑ i, w i * (p i j * Real.log (p i j / FiniteEntropy.mass J (p i) h c)) := by
        apply Finset.sum_le_sum
        intro c _
        apply Finset.sum_le_sum
        intro j hj
        rw [hmass c]
        have hJj := (Finset.mem_filter.mp hj).1
        have hl := h44_lsum Finset.univ (fun i => w i * p i j)
          (fun i => w i * FiniteEntropy.mass J (p i) h c)
          (fun i _ => mul_nonneg (hw i) (hp i j hJj))
          (fun i _ => mul_le_mul_of_nonneg_left (Finset.single_le_sum
            (fun k hk => hp i k (Finset.mem_filter.mp hk).1) hj) (hw i))
        refine hl.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        rcases (hw i).eq_or_lt with h0 | hpos
        · rw [← h0]; simp
        · rw [mul_div_mul_left _ _ hpos.ne']
          ring
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun c _ => Finset.sum_comm), Finset.sum_comm]
theorem h44_fair_eq (μ : Measure ℝ) (v : ℝ) :
    (1/2 : ℝ≥0∞) • μ + (1/2 : ℝ≥0∞) • μ.map (fun x => x+v) = fairShift μ v := by
  unfold fairShift
  rw [Fin.sum_univ_two]
  have h0 : μ.map (fun x => x + (((0 : Fin 2) : ℕ) : ℝ) * v) = μ := by
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
    exact Measure.map_id
  have h1 : (fun x : ℝ => x + (((1 : Fin 2) : ℕ) : ℝ) * v) = fun x => x + v := by
    funext x; simp
  have h2 : ENNReal.ofReal (1/2 : ℝ) = 1/2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  simp only [Fin.val_zero, Fin.val_one] at h0 h1 ⊢
  rw [h0, h1, h2]

theorem h44_fair_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    IsProbabilityMeasure (fairShift μ v) := by
  rw [← h44_fair_eq]
  haveI : IsProbabilityMeasure (μ.map (fun x => x+v)) := Measure.isProbabilityMeasure_map (by fun_prop)
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.add_halves]

theorem h44_fair_cc (μ : Measure ℝ) (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  obtain ⟨B, hB0, hB⟩ := hμ
  refine ⟨B + |v|, by positivity, ?_⟩
  rw [← h44_fair_eq]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have h1 : μ (Set.Icc (-(B + |v|)) (B + |v|))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (by linarith [abs_nonneg v])
      (by linarith [abs_nonneg v]))) hB
  have h2 : μ.map (fun x => x+v) (Set.Icc (-(B + |v|)) (B + |v|))ᶜ = 0 := by
    rw [Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    apply measure_mono_null _ hB
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
    have := neg_abs_le v
    have := le_abs_self v
    rcases hx with h | h
    · left; linarith
    · right; linarith
  rw [h1, h2]
  simp

theorem h44_intobs {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by
  classical
  have hm : ∀ b, MeasurableSet {x | f x = b} := fun b => hf (measurableSet_singleton b)
  have h : ∀ᵐ x ∂μ, F (f x) = ∑ b ∈ s, ({x | f x = b}.indicator (fun _ => F b) x) := by
    filter_upwards [hs] with x hx
    rw [Finset.sum_eq_single (f x)]
    · simp
    · intro b _ hb
      simp [Set.indicator, Ne.symm hb]
    · intro h; exact absurd hx h
  rw [integral_congr_ae h, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro b _
    rw [integral_indicator_const _ (hm b), smul_eq_mul]
    rfl
  · intro b _
    exact (integrable_const _).indicator (hm b)

theorem h44_incr01 {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (y : ℝ) :
    0 ≤ ⌊y + a⌋ - ⌊y⌋ ∧ ⌊y + a⌋ - ⌊y⌋ ≤ 1 := by
  have h1 : ⌊y⌋ ≤ ⌊y + a⌋ := Int.floor_le_floor (by linarith)
  have h2 : ⌊y + a⌋ ≤ ⌊y⌋ + 1 := by
    rw [← Int.floor_add_one]; exact Int.floor_le_floor (by linarith)
  constructor <;> omega

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (u w : ℝ) :
    gridInformation μ v t u ≤ gridInformation μ v s w+
      (∫ x, Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) ∂fairShift μ v)*Real.log 2 := by
  obtain ⟨B, hB0, hB⟩ := hμ
  have hst0 : 0 < s/t := div_pos hs ht
  have hst1 : s/t ≤ 1 := (div_le_one ht).mpr hst
  set ν := μ.map (fun x => x+v) with hνdef
  set m := (1/2 : ℝ≥0∞) • μ + (1/2 : ℝ≥0∞) • ν with hmdef
  haveI hνp : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  haveI hmp : IsProbabilityMeasure m := by
    have := h44_fair_prob μ v
    rwa [← h44_fair_eq] at this
  set B' := B + |v| with hB'
  have hBμ : μ (Set.Icc (-B') B')ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.mpr (Set.Icc_subset_Icc (by linarith [abs_nonneg v])
      (by linarith [abs_nonneg v]))) hB
  have hBν : ν (Set.Icc (-B') B')ᶜ = 0 := by
    rw [hνdef, Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
    apply measure_mono_null _ hB
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx ⊢
    have := neg_abs_le v
    have := le_abs_self v
    rcases hx with h | h
    · left; linarith
    · right; linarith
  have hBm : m (Set.Icc (-B') B')ᶜ = 0 := by
    rw [hmdef]
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hBμ, hBν, mul_zero, add_zero]
  set L := label s w with hL
  set C := label t u with hC
  set z : ℤ → ℝ := fun l => u+((s/t)*(l : ℝ)-(s/t)*w) with hz
  set bad : ℤ → Prop := fun l => Boundary.increment (s/t) (z l) ≠ 0 with hbad
  have hβ : ∀ x, (0 ≤ C x - ⌊z (L x)⌋ ∧ C x - ⌊z (L x)⌋ ≤ 1) ∧
      (¬ bad (L x) → C x - ⌊z (L x)⌋ = 0) := by
    intro x
    have h1 : ((L x : ℤ) : ℝ) ≤ x/s + w := Int.floor_le _
    have h2 : x/s + w < (L x : ℝ) + 1 := Int.lt_floor_add_one _
    have e : x/t = s/t * (x/s) := by field_simp
    have h3 : z (L x) ≤ x/t + u := by
      have := mul_le_mul_of_nonneg_left (show (L x:ℝ) - w ≤ x/s by linarith) hst0.le
      simp only [hz]; rw [e]; linarith
    have h4 : x/t + u < z (L x) + s/t := by
      have := mul_lt_mul_of_pos_left (show x/s < (L x:ℝ) + 1 - w by linarith) hst0
      simp only [hz]; rw [e]; linarith
    have h5 : ⌊z (L x)⌋ ≤ C x := Int.floor_le_floor h3
    have h6 : C x ≤ ⌊z (L x) + s/t⌋ := Int.floor_le_floor h4.le
    have h7 := h44_incr01 hst0 hst1 (z (L x))
    refine ⟨⟨by omega, by omega⟩, fun hnb => ?_⟩
    have : ⌊z (L x) + s/t⌋ = ⌊z (L x)⌋ := by
      by_contra hne
      apply hnb
      simp only [hbad, Boundary.increment]
      have : (⌊z (L x) + s/t⌋ : ℝ) ≠ ⌊z (L x)⌋ := by exact_mod_cast hne
      exact sub_ne_zero.mpr this
    omega
  set φ : ℝ → ℤ × ℤ := fun x => (C x - ⌊z (L x)⌋, L x) with hφdef
  have hφm : Measurable φ := by
    have h2 : Measurable (fun x => (L x, C x)) :=
      (label_measurable s w).prodMk (label_measurable t u)
    have h3 : Measurable (fun r : ℤ × ℤ => (r.2 - ⌊z r.1⌋, r.1)) := measurable_of_countable _
    exact h3.comp h2
  set J := Finset.Icc ⌊-B'/s + w⌋ ⌊B'/s + w⌋ with hJ
  set S : Finset (ℤ × ℤ) := (({0, 1} : Finset ℤ) ×ˢ J).filter (fun a => bad a.2 ∨ a.1 = 0) with hSdef
  have hSa : ∀ ρ : Measure ℝ, ρ (Set.Icc (-B') B')ᶜ = 0 → ∀ᵐ x ∂ρ, φ x ∈ S := by
    intro ρ hρ
    filter_upwards [label_ae_finite ρ (u := w) hs hρ] with x hx
    rw [hSdef, Finset.mem_filter, Finset.mem_product]
    have hb := hβ x
    refine ⟨⟨?_, hx⟩, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      show C x - ⌊z (L x)⌋ = 0 ∨ C x - ⌊z (L x)⌋ = 1
      omega
    · by_cases h : bad (L x)
      · exact Or.inl h
      · exact Or.inr (hb.2 h)
  set G : ℤ × ℤ → ℤ := fun a => ⌊z a.2⌋ + a.1 with hG
  have hGφ : C = G ∘ φ := by
    funext x
    simp only [hG, hφdef, Function.comp_apply]
    ring
  have hLφ : L = Prod.snd ∘ φ := rfl
  have hfacts : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], ρ (Set.Icc (-B') B')ᶜ = 0 →
      entropy ρ C = FiniteEntropy.observableEntropy S (mass ρ φ) G ∧
      entropy ρ L = FiniteEntropy.observableEntropy S (mass ρ φ) Prod.snd ∧
      FiniteEntropy.entropy S (mass ρ φ) =
        FiniteEntropy.observableEntropy S (mass ρ φ) (fun a => (a.1, a.2)) ∧
      FiniteEntropy.observableEntropy S (mass ρ φ) Prod.snd ≤ FiniteEntropy.entropy S (mass ρ φ) ∧
      FiniteEntropy.entropy S (mass ρ φ) - FiniteEntropy.observableEntropy S (mass ρ φ) G =
        -∑ c ∈ S.image G, ∑ j ∈ S.filter (fun j => G j = c),
          mass ρ φ j * Real.log (mass ρ φ j / FiniteEntropy.mass S (mass ρ φ) G c) := by
    intro ρ _ hρ
    have ha := hSa ρ hρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hGφ]; exact h44_mentcomp ρ φ hφm S ha G
    · rw [hLφ]; exact h44_mentcomp ρ φ hφm S ha Prod.snd
    · rw [← h44_mentfin ρ φ S ha]
      exact h44_mentcomp ρ φ hφm S ha (fun a => (a.1, a.2))
    · exact h44_fdp S _ (fun a _ => mass_nonneg ρ φ a) Prod.snd
    · exact h44_Dform S G _ (fun j _ => mass_nonneg ρ φ j)
  obtain ⟨cμ1, cμ2, cμ3, cμ4, cμ5⟩ := hfacts μ hBμ
  obtain ⟨cν1, cν2, cν3, cν4, cν5⟩ := hfacts ν hBν
  obtain ⟨cm1, cm2, cm3, cm4, cm5⟩ := hfacts m hBm
  have hmix : mass m φ = fun k => ∑ i : Fin 2, (fun _ => (1/2 : ℝ)) i * (![mass μ φ, mass ν φ] i k) := by
    funext k
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold mass
    rw [hmdef]
    simp only [Measure.real_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul]
    norm_num
  have hc := h44_conc S G ![mass μ φ, mass ν φ]
    (by intro i j _; fin_cases i <;> simp [mass_nonneg]) (fun _ => (1/2 : ℝ)) (fun _ => by norm_num)
  have hmix' : ∀ j, (1/2 : ℝ) * mass μ φ j + 1/2 * mass ν φ j = mass m φ j := by
    intro j
    have := congrFun hmix j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    exact this.symm
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    hmix'] at hc
  have hbm := h44_badmass S (mass m φ) Prod.fst Prod.snd bad (fun a _ => mass_nonneg m φ a) (by
    intro a ha b hb hab hna
    rw [hSdef, Finset.mem_filter] at ha hb
    rw [ha.2.resolve_left hna, hb.2.resolve_left (hab ▸ hna)])
  unfold FiniteEntropy.conditionalEntropy at hbm
  have hcard : (S.image Prod.fst).card ≤ 2 := by
    have himg : S.image Prod.fst ⊆ ({0, 1} : Finset ℤ) := by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
      rw [hSdef, Finset.mem_filter, Finset.mem_product] at ha
      exact ha.1.1
    exact (Finset.card_le_card himg).trans (by decide)
  have hlog : Real.log ((S.image Prod.fst).card : ℝ) ≤ Real.log 2 := by
    rcases Nat.eq_zero_or_pos (S.image Prod.fst).card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)
  have hnn : 0 ≤ ∑ a ∈ S, if bad a.2 then mass m φ a else 0 :=
    Finset.sum_nonneg fun a ha => by split_ifs <;> simp [mass_nonneg]
  have hbm2 := hbm.trans (mul_le_mul_of_nonneg_left hlog hnn)
  have hI : (∫ x, Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) ∂fairShift μ v) =
      ∑ a ∈ S, if bad a.2 then mass m φ a else 0 := by
    rw [← h44_fair_eq μ v]
    show ∫ x, Boundary.increment (s/t) (z (L x)) ∂m = _
    have hpt : ∀ x, Boundary.increment (s/t) (z (L x)) =
        (fun a : ℤ × ℤ => if bad a.2 then (1 : ℝ) else 0) (φ x) := by
      intro x
      show Boundary.increment (s/t) (z (L x)) = if bad (L x) then (1 : ℝ) else 0
      by_cases hb : bad (L x)
      · rw [if_pos hb]
        have h7 := h44_incr01 hst0 hst1 (z (L x))
        have hne : ⌊z (L x) + s/t⌋ - ⌊z (L x)⌋ ≠ 0 := by
          intro h0
          apply hb
          simp only [hbad, Boundary.increment]
          have : (⌊z (L x) + s/t⌋ : ℝ) = ⌊z (L x)⌋ := by exact_mod_cast (by omega : ⌊z (L x) + s/t⌋ = ⌊z (L x)⌋)
          rw [this, sub_self]
        have h1 : ⌊z (L x) + s/t⌋ - ⌊z (L x)⌋ = 1 := by omega
        simp only [Boundary.increment]
        have : ((⌊z (L x) + s/t⌋ - ⌊z (L x)⌋ : ℤ) : ℝ) = 1 := by rw [h1]; simp
        push_cast at this
        exact this
      · rw [if_neg hb]
        simp only [hbad, not_not] at hb
        exact hb
    refine (integral_congr_ae (Filter.Eventually.of_forall hpt)).trans
      ((h44_intobs m φ hφm S (hSa m hBm) (fun a : ℤ × ℤ => if bad a.2 then (1 : ℝ) else 0)).trans
        (Finset.sum_congr rfl fun a _ => ?_))
    split_ifs <;> simp
  have e1 : gridInformation μ v t u = entropy m C - (entropy μ C + entropy ν C)/2 := rfl
  have e2 : gridInformation μ v s w = entropy m L - (entropy μ L + entropy ν L)/2 := rfl
  rw [e1, e2, hI, cμ1, cν1, cm1, cμ2, cν2, cm2]
  have hc' : ∑ c ∈ S.image G, ∑ j ∈ S.filter (fun j => G j = c),
        mass m φ j * Real.log (mass m φ j / FiniteEntropy.mass S (mass m φ) G c) ≤
      1 / 2 * ∑ c ∈ S.image G, ∑ j ∈ S.filter (fun j => G j = c),
          mass μ φ j * Real.log (mass μ φ j / FiniteEntropy.mass S (mass μ φ) G c) +
      1 / 2 * ∑ c ∈ S.image G, ∑ j ∈ S.filter (fun j => G j = c),
          mass ν φ j * Real.log (mass ν φ j / FiniteEntropy.mass S (mass ν φ) G c) := hc
  linarith

