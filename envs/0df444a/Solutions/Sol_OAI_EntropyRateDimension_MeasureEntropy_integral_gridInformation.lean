-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:49:08.955774+00:00
-- url     : https://prove2.me/submissions/dd667522-ee21-4903-9e02-1c6b52900369

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

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u in (0 : ℝ)..1, gridInformation μ v s u) = averaged (fairShift μ v) s-averaged μ s := by
  haveI := h44_fair_prob μ v
  have hpt : ∀ u, gridInformation μ v s u =
      grid (fairShift μ v) s u - (grid μ s u + grid μ s (u + v/s))/2 := by
    intro u
    unfold gridInformation information
    rw [h44_fair_eq, h44_grid_map μ hs.ne']
    rfl
  have hA := h44_grid_ii (fairShift μ v) (h44_fair_cc μ hμ v) hs 0 1
  have hg := h44_grid_ii μ hμ hs 0 1
  have hg' : IntervalIntegrable (fun u => grid μ s (u + v/s)) volume 0 1 := by
    simpa using (h44_grid_ii μ hμ hs (0 + v/s) (1 + v/s)).comp_add_right (v/s)
  rw [intervalIntegral.integral_congr (fun u _ => hpt u),
    intervalIntegral.integral_sub hA ((hg.add hg').div_const 2), intervalIntegral.integral_div,
    intervalIntegral.integral_add hg hg', h44_int_shift, h44_avg_eq, h44_avg_eq]
  ring

