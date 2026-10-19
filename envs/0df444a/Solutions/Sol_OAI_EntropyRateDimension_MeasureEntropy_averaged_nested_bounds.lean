-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:54:28.298338+00:00
-- url     : https://prove2.me/submissions/d478e250-d884-4270-a7e0-05441f9b3a76

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

theorem h44_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℤ) (j : ℤ) :
    mass ν f j ≤ 1 := by
  unfold mass
  exact measureReal_le_one

theorem h44_grid_ii (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν)
    {s : ℝ} (hs : 0 < s) (a b : ℝ) : IntervalIntegrable (grid ν s) volume a b := by
  obtain ⟨B, hB0, hB⟩ := hν
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  set lo := min a b
  set hi := max a b
  set J : Finset ℤ := Finset.Icc ⌊-B/s + lo⌋ ⌊B/s + hi⌋ with hJ
  set F : ℝ → ℝ := fun u => ∑ j ∈ J, Real.negMulLog (mass ν (label s u) j) with hF
  have hEq : Set.EqOn F (grid ν s) (Set.Icc lo hi) := by
    intro u hu
    have hae : ∀ᵐ x ∂ν, label s u x ∈ J := (label_ae_finite ν (u := u) hs hB).mono fun x hx => by
      rw [Finset.mem_Icc] at hx ⊢
      exact ⟨le_trans (Int.floor_le_floor (by linarith [hu.1])) hx.1,
        le_trans hx.2 (Int.floor_le_floor (by linarith [hu.2]))⟩
    show F u = entropy ν (label s u)
    rw [h44_mentfin ν _ J hae]
    rfl
  have hm : ∀ j : ℤ, Measurable (fun u => mass ν (label s u) j) := by
    intro j
    have hE : MeasurableSet {p : ℝ × ℝ | ⌊p.2 / s + p.1⌋ = j} :=
      (((measurable_snd.div_const s).add measurable_fst).floor) (measurableSet_singleton j)
    exact (measurable_measure_prodMk_left hE).ennreal_toReal
  have hFm : Measurable F :=
    Finset.measurable_sum _ (fun j _ => Real.continuous_negMulLog.measurable.comp (hm j))
  have hFI : IntegrableOn F (Set.Icc lo hi) volume := by
    refine Measure.integrableOn_of_bounded (M := (J.card : ℝ)) (by simp)
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      Real.negMulLog_nonneg (mass_nonneg _ _ _) (h44_mass_le_one _ _ _))]
    calc F u ≤ ∑ j ∈ J, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
            have := Real.negMulLog_le_one_sub_self (mass_nonneg ν (label s u) j)
            linarith [mass_nonneg ν (label s u) j]
      _ = J.card := by simp
  exact hFI.congr_fun hEq measurableSet_Icc

theorem h44_ment_inj {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℤ)
    (h : ℤ → ℤ) (hinj : Function.Injective h) : entropy μ (h ∘ f) = entropy μ f := by
  unfold entropy
  rw [← hinj.tsum_eq]
  · congr 1
    ext b
    congr 1
    unfold mass
    congr 1
    ext x
    exact hinj.eq_iff
  · intro c hc
    by_contra hr
    apply hc
    show Real.negMulLog (mass μ (h ∘ f) c) = 0
    have : {x | (h ∘ f) x = c} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Function.comp_apply]
      exact fun hx => hr ⟨f x, hx⟩
    unfold mass
    rw [this]
    simp

theorem h44_grid_per (μ : Measure ℝ) (s : ℝ) : Function.Periodic (grid μ s) 1 := by
  intro u
  unfold grid
  have : label s (u + 1) = (fun j => j + 1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [this, h44_ment_inj μ _ _ (fun a b h => by simpa using h)]

theorem h44_grid_map (μ : Measure ℝ) {s : ℝ} (hs : s ≠ 0) (u v : ℝ) :
    entropy (μ.map (fun x => x+v)) (label s u) = grid μ s (u + v/s) := by
  unfold grid entropy
  congr 1
  ext j
  congr 1
  unfold mass
  simp only [Measure.real_def]
  rw [Measure.map_apply (s := {x | label s u x = j}) (by fun_prop)
    (label_measurable s u (measurableSet_singleton j))]
  congr 2
  ext x
  show ⌊(x+v)/s+u⌋ = j ↔ ⌊x/s+(u+v/s)⌋ = j
  rw [show (x+v)/s+u = x/s+(u+v/s) by field_simp; ring]

theorem h44_avg_eq (ν : Measure ℝ) (s : ℝ) :
    averaged ν s = ∫ u in (0:ℝ)..1, grid ν s u := by
  unfold averaged
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem h44_int_shift (μ : Measure ℝ) (s c : ℝ) :
    ∫ u in (0:ℝ)..1, grid μ s (u + c) = ∫ u in (0:ℝ)..1, grid μ s u := by
  rw [intervalIntegral.integral_comp_add_right]
  have := (h44_grid_per μ s).intervalIntegral_add_eq c 0
  simp only [zero_add] at this
  rw [zero_add, add_comm 1 c]
  exact this

theorem h44_ptb (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    grid μ ((N : ℝ)*s) u ≤ grid μ s ((N : ℝ)*u) ∧
      grid μ s ((N : ℝ)*u) ≤ grid μ ((N : ℝ)*s) u + Real.log N := by
  classical
  obtain ⟨B, hB0, hB⟩ := hμ
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  set fine := label s ((N : ℝ)*u) with hfine
  have hcf : label ((N:ℝ)*s) u = (fun j : ℤ => j / (N:ℤ)) ∘ fine := by
    funext x
    simp only [hfine, label, Function.comp_apply]
    rw [← Int.floor_div_natCast]
    congr 1
    field_simp
  set Sf := Finset.Icc ⌊-B/s + (N:ℝ)*u⌋ ⌊B/s + (N:ℝ)*u⌋ with hSf
  have hSfa : ∀ᵐ x ∂μ, fine x ∈ Sf := label_ae_finite μ hs hB
  have hfm : Measurable fine := label_measurable _ _
  constructor
  · unfold grid
    rw [hcf, h44_mentcomp μ fine hfm Sf hSfa, h44_mentfin μ fine Sf hSfa]
    exact h44_fdp Sf _ (fun a _ => mass_nonneg μ fine a) _
  · set Ψ : ℤ → ℤ × ℤ := fun j => (j % (N:ℤ), j / (N:ℤ)) with hΨ
    set φ := Ψ ∘ fine with hφdef
    set S := Sf.image Ψ with hSdef
    have hSa : ∀ᵐ x ∂μ, φ x ∈ S := hSfa.mono fun x hx => Finset.mem_image_of_mem Ψ hx
    have hφm : Measurable φ := (measurable_of_countable Ψ).comp hfm
    set P := mass μ φ with hP
    have hPnn : ∀ a ∈ S, 0 ≤ P a := fun a _ => mass_nonneg μ φ a
    set G : ℤ × ℤ → ℤ := fun r => r.1 + (N:ℤ) * r.2 with hG
    have hGφ : fine = G ∘ φ := by
      funext x
      simp only [hG, hφdef, hΨ, Function.comp_apply]
      exact (Int.emod_add_mul_ediv _ _).symm
    have hcs : label ((N:ℝ)*s) u = Prod.snd ∘ φ := by rw [hcf]; rfl
    have h1 : grid μ s ((N:ℝ)*u) = FiniteEntropy.observableEntropy S P G := by
      unfold grid; rw [← hfine, hGφ]; exact h44_mentcomp μ φ hφm S hSa G
    have h2 : grid μ ((N:ℝ)*s) u = FiniteEntropy.observableEntropy S P Prod.snd := by
      unfold grid; rw [hcs]; exact h44_mentcomp μ φ hφm S hSa Prod.snd
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
    have hcard : (S.image Prod.fst).card ≤ N := by
      have himg : S.image Prod.fst ⊆ Finset.Ico (0 : ℤ) N := by
        intro r hr
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
        rw [Finset.mem_Ico]
        exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      have := Finset.card_le_card himg
      rw [Int.card_Ico] at this
      omega
    have hlog : Real.log ((S.image Prod.fst).card : ℝ) ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos (S.image Prod.fst).card with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg N
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hcard)
    rw [h1, h2]
    linarith

theorem h44_int_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    ∫ u in (0:ℝ)..1, grid μ s ((N:ℝ)*u) = ∫ u in (0:ℝ)..1, grid μ s u := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [intervalIntegral.integral_comp_mul_left (grid μ s) hN'.ne']
  have := (h44_grid_per μ s).intervalIntegral_add_zsmul_eq (N : ℤ) 0 (h44_grid_ii μ hμ hs)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at this
  rw [mul_zero, mul_one, this, smul_eq_mul]
  field_simp

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    0 ≤ averaged μ s-averaged μ ((N : ℝ)*s) ∧
      averaged μ s-averaged μ ((N : ℝ)*s) ≤ Real.log N := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hNs : 0 < (N:ℝ)*s := mul_pos hN' hs
  have hA : IntervalIntegrable (fun u => grid μ s ((N:ℝ)*u)) volume 0 1 := by
    have := (h44_grid_ii μ hμ hs 0 N).comp_mul_left (c := (N:ℝ))
    rwa [zero_div, div_self hN'.ne'] at this
  have hB := h44_grid_ii μ hμ hNs 0 1
  have e1 : averaged μ s = ∫ u in (0:ℝ)..1, grid μ s ((N:ℝ)*u) := by
    rw [h44_avg_eq, h44_int_scale μ hμ hs hN]
  have e2 := h44_avg_eq μ ((N:ℝ)*s)
  rw [e1, e2]
  constructor
  · rw [sub_nonneg]
    exact intervalIntegral.integral_mono_on zero_le_one hB hA
      (fun u _ => (h44_ptb μ hμ hs hN u).1)
  · have hle : ∫ u in (0:ℝ)..1, grid μ s ((N:ℝ)*u) ≤
        ∫ u in (0:ℝ)..1, (grid μ ((N:ℝ)*s) u + Real.log N) :=
      intervalIntegral.integral_mono_on zero_le_one hA (hB.add intervalIntegrable_const)
        (fun u _ => (h44_ptb μ hμ hs hN u).2)
    rw [intervalIntegral.integral_add hB intervalIntegrable_const,
      intervalIntegral.integral_const] at hle
    simp only [sub_zero, one_smul] at hle
    linarith

