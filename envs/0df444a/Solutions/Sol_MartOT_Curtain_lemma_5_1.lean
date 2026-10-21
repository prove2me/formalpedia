-- Prove2me | solution 1 for MartOT.Curtain.lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:41:59.384894+00:00
-- url     : https://prove2.me/submissions/3bd7ef0e-154c-4ae5-9e9b-29cba5d9bbd4

import Mathlib
import Definitions.Def_MartOT_Var_Setting

set_option autoImplicit false
open MeasureTheory Filter Topology

namespace MCL51

lemma ce_nonneg {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) (φ : ℝ → ℝ)
    (hφ : ConvexOn ℝ Set.univ φ) (h0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂ν := by
  have key : ∀ m : Measure ℝ, MartOT.Var.integralE m φ
      = ((∫⁻ x, ENNReal.ofReal (φ x) ∂m : ENNReal) : EReal) := by
    intro m
    unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
    have h2 : ∀ x, ENNReal.ofReal (-φ x) = 0 := fun x =>
      ENNReal.ofReal_of_nonpos (by linarith [h0 x])
    simp [h2]
  have := h.2.2 φ hφ
  rw [key, key] at this
  exact_mod_cast this

lemma convex_reluR (c : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => max (x - c) 0) := by
  refine ConvexOn.sup ?_ ?_
  · exact (convexOn_id convex_univ).sub (concaveOn_const c convex_univ)
  · exact convexOn_const 0 convex_univ

lemma convex_reluL (c : ℝ) : ConvexOn ℝ Set.univ (fun x : ℝ => max (c - x) 0) := by
  refine ConvexOn.sup ?_ ?_
  · exact (convexOn_const c convex_univ).sub (concaveOn_id convex_univ)
  · exact convexOn_const 0 convex_univ

lemma posR {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) (a : ℝ)
    (hμ : 0 < μ (Set.Ioi a)) : 0 < ν (Set.Ioi a) := by
  by_contra hν
  have hν0 : ν (Set.Ioi a) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hν)
  have hle := ce_nonneg h _ (convex_reluR a) (fun x => le_max_right _ _)
  have hνz : ∫⁻ x, ENNReal.ofReal (max (x - a) 0) ∂ν = 0 := by
    have : ∀ᵐ x ∂ν, x ∉ Set.Ioi a := measure_eq_zero_iff_ae_notMem.mp hν0
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · filter_upwards [this] with x hx
      have : x - a ≤ 0 := by simpa using hx
      simp [this]
  have hz : ∫⁻ x, ENNReal.ofReal (max (x - a) 0) ∂μ = 0 :=
    le_antisymm (hνz ▸ hle) bot_le
  rw [lintegral_eq_zero_iff (by fun_prop)] at hz
  have : μ (Set.Ioi a) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hz] with x hx
    have hx' : ENNReal.ofReal (max (x - a) 0) = 0 := hx
    rw [ENNReal.ofReal_eq_zero] at hx'
    intro hxa
    have : a < x := hxa
    have := le_max_left (x - a) 0
    linarith
  exact absurd hμ (by simp [this])

lemma posL {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) (a : ℝ)
    (hμ : 0 < μ (Set.Iio a)) : 0 < ν (Set.Iio a) := by
  by_contra hν
  have hν0 : ν (Set.Iio a) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hν)
  have hle := ce_nonneg h _ (convex_reluL a) (fun x => le_max_right _ _)
  have hνz : ∫⁻ x, ENNReal.ofReal (max (a - x) 0) ∂ν = 0 := by
    have : ∀ᵐ x ∂ν, x ∉ Set.Iio a := measure_eq_zero_iff_ae_notMem.mp hν0
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · filter_upwards [this] with x hx
      have : a - x ≤ 0 := by simpa using hx
      simp [this]
  have hz : ∫⁻ x, ENNReal.ofReal (max (a - x) 0) ∂μ = 0 :=
    le_antisymm (hνz ▸ hle) bot_le
  rw [lintegral_eq_zero_iff (by fun_prop)] at hz
  have : μ (Set.Iio a) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hz] with x hx
    have hx' : ENNReal.ofReal (max (a - x) 0) = 0 := hx
    rw [ENNReal.ofReal_eq_zero] at hx'
    intro hxa
    have : x < a := hxa
    have := le_max_left (a - x) 0
    linarith
  exact absurd hμ (by simp [this])

lemma atomR {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) [IsFiniteMeasure ν] (a : ℝ)
    (hν0 : ν (Set.Ioi a) = 0) : μ {a} ≤ ν {a} := by
  have hε : ∀ ε : ℝ, 0 < ε → μ {a} ≤ ν (Set.Ioc (a - ε) a) := by
    intro ε hε
    have hle := ce_nonneg h _ (convex_reluR (a - ε)) (fun x => le_max_right _ _)
    have h1 : ENNReal.ofReal ε * μ {a} ≤
        ∫⁻ x, ENNReal.ofReal (max (x - (a - ε)) 0) ∂μ := by
      rw [← lintegral_indicator_const (measurableSet_singleton a)]
      refine lintegral_mono fun x => ?_
      by_cases hx : x = a
      · subst hx; simp [Set.indicator, le_refl]
      · simp [Set.indicator, hx]
    have h2 : ∫⁻ x, ENNReal.ofReal (max (x - (a - ε)) 0) ∂ν ≤
        ENNReal.ofReal ε * ν (Set.Ioc (a - ε) a) := by
      rw [← lintegral_indicator_const measurableSet_Ioc]
      have : ∀ᵐ x ∂ν, x ∉ Set.Ioi a := measure_eq_zero_iff_ae_notMem.mp hν0
      refine lintegral_mono_ae ?_
      filter_upwards [this] with x hx
      have hxa : x ≤ a := by simpa using hx
      by_cases hx2 : a - ε < x
      · have : x ∈ Set.Ioc (a - ε) a := ⟨hx2, hxa⟩
        simp only [Set.indicator_of_mem this]
        exact ENNReal.ofReal_le_ofReal (max_le (by linarith) hε.le)
      · have : x - (a - ε) ≤ 0 := by linarith
        simp [this]
    have h3 := h1.trans (hle.trans h2)
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hε) ENNReal.ofReal_ne_top).mp h3
  have hlim : Tendsto (fun n : ℕ => ν (Set.Ioc (a - 1 / ((n : ℝ) + 1)) a)) atTop
      (𝓝 (ν {a})) := by
    have hset : (⋂ n : ℕ, Set.Ioc (a - 1 / ((n : ℝ) + 1)) a) = {a} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · rintro hx
        have hxa : x ≤ a := (hx 0).2
        by_contra hne
        have hlt : x < a := lt_of_le_of_ne hxa hne
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have := (hx n).1
        linarith
      · rintro rfl n
        refine ⟨?_, le_rfl⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [← hset]
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Ioc.nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro m n hmn
    refine Set.Ioc_subset_Ioc_left ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  exact ge_of_tendsto' hlim (fun n => hε _ (by positivity))

lemma atomL {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) [IsFiniteMeasure ν] (a : ℝ)
    (hν0 : ν (Set.Iio a) = 0) : μ {a} ≤ ν {a} := by
  have hε : ∀ ε : ℝ, 0 < ε → μ {a} ≤ ν (Set.Ico a (a + ε)) := by
    intro ε hε
    have hle := ce_nonneg h _ (convex_reluL (a + ε)) (fun x => le_max_right _ _)
    have h1 : ENNReal.ofReal ε * μ {a} ≤
        ∫⁻ x, ENNReal.ofReal (max ((a + ε) - x) 0) ∂μ := by
      rw [← lintegral_indicator_const (measurableSet_singleton a)]
      refine lintegral_mono fun x => ?_
      by_cases hx : x = a
      · subst hx; simp [Set.indicator, le_refl]
      · simp [Set.indicator, hx]
    have h2 : ∫⁻ x, ENNReal.ofReal (max ((a + ε) - x) 0) ∂ν ≤
        ENNReal.ofReal ε * ν (Set.Ico a (a + ε)) := by
      rw [← lintegral_indicator_const measurableSet_Ico]
      have : ∀ᵐ x ∂ν, x ∉ Set.Iio a := measure_eq_zero_iff_ae_notMem.mp hν0
      refine lintegral_mono_ae ?_
      filter_upwards [this] with x hx
      have hxa : a ≤ x := by simpa using hx
      by_cases hx2 : x < a + ε
      · have : x ∈ Set.Ico a (a + ε) := ⟨hxa, hx2⟩
        simp only [Set.indicator_of_mem this]
        exact ENNReal.ofReal_le_ofReal (max_le (by linarith) hε.le)
      · have : (a + ε) - x ≤ 0 := by linarith
        simp [this]
    have h3 := h1.trans (hle.trans h2)
    exact (ENNReal.mul_le_mul_iff_right (by simpa using hε) ENNReal.ofReal_ne_top).mp h3
  have hlim : Tendsto (fun n : ℕ => ν (Set.Ico a (a + 1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ν {a})) := by
    have hset : (⋂ n : ℕ, Set.Ico a (a + 1 / ((n : ℝ) + 1))) = {a} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Ico, Set.mem_singleton_iff]
      constructor
      · rintro hx
        have hxa : a ≤ x := (hx 0).1
        by_contra hne
        have hlt : a < x := lt_of_le_of_ne hxa (Ne.symm hne)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        have := (hx n).2
        linarith
      · rintro rfl n
        refine ⟨le_rfl, ?_⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [← hset]
    refine tendsto_measure_iInter_atTop (fun n => measurableSet_Ico.nullMeasurableSet) ?_
      ⟨0, measure_ne_top _ _⟩
    intro m n hmn
    refine Set.Ico_subset_Ico_right ?_
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  exact ge_of_tendsto' hlim (fun n => hε _ (by positivity))

end MCL51

open MCL51 in
theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) :
    ((∀ a : ℝ, 0 < μ (Set.Ioi a) ∧ 0 < ν (Set.Ioi a)) ∨
      (BddAbove μ.support ∧ 0 < ν (Set.Ioi (sSup μ.support))) ∨
      (BddAbove μ.support ∧ ν (Set.Ioi (sSup μ.support)) = 0 ∧
        μ {sSup μ.support} ≤ ν {sSup μ.support})) ∧
    ((∀ b : ℝ, 0 < μ (Set.Iio b) ∧ 0 < ν (Set.Iio b)) ∨
      (BddBelow μ.support ∧ 0 < ν (Set.Iio (sInf μ.support))) ∨
      (BddBelow μ.support ∧ ν (Set.Iio (sInf μ.support)) = 0 ∧
        μ {sInf μ.support} ≤ ν {sInf μ.support})) := by
  haveI : IsFiniteMeasure μ := hμν.1.1
  haveI : IsFiniteMeasure ν := hμν.2.1.1
  constructor
  · by_cases hb : BddAbove μ.support
    · right
      set s := sSup μ.support with hs
      have hμs : μ (Set.Ioi s) = 0 := by
        have hsub : Set.Ioi s ⊆ μ.supportᶜ := fun x hx hx' =>
          absurd (le_csSup hb hx') (not_le.mpr hx)
        exact measure_mono_null hsub Measure.measure_compl_support
      by_cases hν : 0 < ν (Set.Ioi s)
      · exact Or.inl ⟨hb, hν⟩
      · exact Or.inr ⟨hb, nonpos_iff_eq_zero.mp (not_lt.mp hν), atomR hμν s
          (nonpos_iff_eq_zero.mp (not_lt.mp hν))⟩
    · left
      intro a
      have hμa : 0 < μ (Set.Ioi a) := by
        by_contra hc
        have h0 : μ (Set.Ioi a) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hc)
        apply hb
        refine ⟨a, fun x hx => ?_⟩
        by_contra hxa
        exact (Measure.subset_compl_support_of_isOpen isOpen_Ioi h0 (not_le.mp hxa)) hx
      exact ⟨hμa, posR hμν a hμa⟩
  · by_cases hb : BddBelow μ.support
    · right
      set s := sInf μ.support with hs
      have hμs : μ (Set.Iio s) = 0 := by
        have hsub : Set.Iio s ⊆ μ.supportᶜ := fun x hx hx' =>
          absurd (csInf_le hb hx') (not_le.mpr hx)
        exact measure_mono_null hsub Measure.measure_compl_support
      by_cases hν : 0 < ν (Set.Iio s)
      · exact Or.inl ⟨hb, hν⟩
      · exact Or.inr ⟨hb, nonpos_iff_eq_zero.mp (not_lt.mp hν), atomL hμν s
          (nonpos_iff_eq_zero.mp (not_lt.mp hν))⟩
    · left
      intro a
      have hμa : 0 < μ (Set.Iio a) := by
        by_contra hc
        have h0 : μ (Set.Iio a) = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hc)
        apply hb
        refine ⟨a, fun x hx => ?_⟩
        by_contra hxa
        exact (Measure.subset_compl_support_of_isOpen isOpen_Iio h0 (not_le.mp hxa)) hx
      exact ⟨hμa, posL hμν a hμa⟩
