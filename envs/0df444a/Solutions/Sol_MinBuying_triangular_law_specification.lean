-- Prove2me | solution 1 for MinBuying.triangular_law_specification
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:19:05.790398+00:00
-- url     : https://prove2.me/submissions/05dddb2e-ab2d-41e8-bb78-852ed95527e7

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory Set MinBuying
noncomputable section

private lemma unit_probability : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  simp [unitIntervalLaw, Real.volume_Ioo]

private lemma tri_measurable (a v : ℝ) : Measurable (fun u : ℝ => min v (a * u / (1 - u))) := by
  fun_prop

private lemma tri_probability (a v : ℝ) : IsProbabilityMeasure (triangularLaw a v) := by
  letI := unit_probability
  exact Measure.isProbabilityMeasure_map (tri_measurable a v).aemeasurable

private lemma tri_support (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ∀ᵐ x ∂triangularLaw a v, x ∈ Icc (0 : ℝ) v := by
  unfold triangularLaw
  apply (ae_map_iff (tri_measurable a v).aemeasurable
    (p := fun x => x ∈ Icc (0 : ℝ) v) measurableSet_Icc).mpr
  have hu : ∀ᵐ u ∂unitIntervalLaw, u ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  filter_upwards [hu] with u hu
  have hd : 0 < 1 - u := sub_pos.mpr hu.2
  exact ⟨le_min hv.le (div_nonneg (mul_nonneg ha.le hu.1.le) hd.le), min_le_left _ _⟩

private lemma tri_strict_interior (a v p : ℝ) (ha : 0 < a) (hp : 0 ≤ p) (hpv : p ≤ v) :
    rejection (triangularLaw a v) p = p / (p + a) := by
  have hpa : 0 < p + a := by positivity
  have hr0 : 0 ≤ p / (p + a) := div_nonneg hp hpa.le
  have hr1 : p / (p + a) < 1 := (div_lt_one hpa).mpr (by linarith)
  have hset : (fun u : ℝ => min v (a * u / (1 - u))) ⁻¹' Iio p ∩ Ioo 0 1 =
      Ioo 0 (p / (p + a)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_Ioo]
    constructor
    · rintro ⟨hmin, hu0, hu1⟩
      have hdiv : a * u / (1 - u) < p :=
        (min_lt_iff.mp hmin).resolve_left (not_lt_of_ge hpv)
      have hh := (div_lt_iff₀ (sub_pos.mpr hu1)).mp hdiv
      exact ⟨hu0, (lt_div_iff₀ hpa).mpr (by nlinarith)⟩
    · rintro ⟨hu0, hur⟩
      have hu1 : u < 1 := hur.trans hr1
      have hh := (lt_div_iff₀ hpa).mp hur
      refine ⟨min_lt_iff.mpr (Or.inr ?_), hu0, hu1⟩
      apply (div_lt_iff₀ (sub_pos.mpr hu1)).mpr
      nlinarith
  unfold rejection triangularLaw unitIntervalLaw
  rw [Measure.map_apply (tri_measurable a v) measurableSet_Iio,
    Measure.restrict_apply ((tri_measurable a v) measurableSet_Iio), hset]
  rw [Real.volume_Ioo]
  simpa using ENNReal.toReal_ofReal hr0

private lemma tri_cdf_interior (a v p : ℝ) (ha : 0 < a) (hp : 0 ≤ p) (hpv : p < v) :
    cdf (triangularLaw a v) p = p / (p + a) := by
  have hpa : 0 < p + a := by positivity
  have hr0 : 0 ≤ p / (p + a) := div_nonneg hp hpa.le
  have hr1 : p / (p + a) < 1 := (div_lt_one hpa).mpr (by linarith)
  have hset : (fun u : ℝ => min v (a * u / (1 - u))) ⁻¹' Iic p ∩ Ioo 0 1 =
      Ioc 0 (p / (p + a)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, mem_Ioc]
    constructor
    · rintro ⟨hmin, hu0, hu1⟩
      have hdiv : a * u / (1 - u) ≤ p :=
        (min_le_iff.mp hmin).resolve_left (not_le_of_gt hpv)
      have hh := (div_le_iff₀ (sub_pos.mpr hu1)).mp hdiv
      exact ⟨hu0, (le_div_iff₀ hpa).mpr (by nlinarith)⟩
    · rintro ⟨hu0, hur⟩
      have hu1 : u < 1 := hur.trans_lt hr1
      have hh := (le_div_iff₀ hpa).mp hur
      refine ⟨min_le_iff.mpr (Or.inr ?_), hu0, hu1⟩
      apply (div_le_iff₀ (sub_pos.mpr hu1)).mpr
      nlinarith
  unfold cdf triangularLaw unitIntervalLaw
  rw [Measure.map_apply (tri_measurable a v) measurableSet_Iic,
    Measure.restrict_apply ((tri_measurable a v) measurableSet_Iic), hset]
  rw [Real.volume_Ioc]
  simpa using ENNReal.toReal_ofReal hr0


private lemma tri_rejection_all (a v : ℝ) (ha : 0 < a) (hv : 0 < v) (p : ℝ) :
    rejection (triangularLaw a v) p = triangularReject a v p := by
  letI := tri_probability a v
  have hs := tri_support a v ha hv
  unfold triangularReject
  split_ifs with hp hpv
  · have hz : triangularLaw a v (Iio p) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hs] with x hx
      exact not_lt_of_ge (hp.trans hx.1)
    simp [rejection, hz]
  · exact tri_strict_interior a v p ha (le_of_not_ge hp) hpv
  · have heq : triangularLaw a v (Iio p) = triangularLaw a v Set.univ := by
      apply measure_congr
      filter_upwards [hs] with x hx
      change (x < p) = True
      apply propext
      exact iff_true_intro (hx.2.trans_lt (lt_of_not_ge hpv))
    simp [rejection, heq]

private lemma tri_cdf_all (a v : ℝ) (ha : 0 < a) (hv : 0 < v) (p : ℝ) :
    cdf (triangularLaw a v) p = triangularCDF a v p := by
  letI := tri_probability a v
  have hs := tri_support a v ha hv
  unfold triangularCDF
  split_ifs with hp hpv
  · have hz : triangularLaw a v (Iic p) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hs] with x hx
      exact not_le_of_gt (hp.trans_le hx.1)
    simp [cdf, hz]
  · exact tri_cdf_interior a v p ha (le_of_not_gt hp) hpv
  · have heq : triangularLaw a v (Iic p) = triangularLaw a v Set.univ := by
      apply measure_congr
      filter_upwards [hs] with x hx
      change (x ≤ p) = True
      apply propext
      exact iff_true_intro (hx.2.trans (le_of_not_gt hpv))
    simp [cdf, heq]

private lemma tri_atom (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ((triangularLaw a v) {v}).toReal = a / (a + v) := by
  letI := tri_probability a v
  have heq : triangularLaw a v {v} = triangularLaw a v (Ici v) := by
    apply measure_congr
    filter_upwards [tri_support a v ha hv] with x hx
    change (x = v) = (v ≤ x)
    apply propext
    exact ⟨fun h => h ▸ le_rfl, fun h => le_antisymm hx.2 h⟩
  rw [heq]
  have htail := probReal_compl_eq_one_sub (μ := triangularLaw a v)
    (s := Iio v) measurableSet_Iio
  have ht : ((triangularLaw a v) (Ici v)).toReal = 1 - rejection (triangularLaw a v) v := by
    simpa [Measure.real, rejection] using htail
  rw [ht, tri_strict_interior a v v ha hv.le le_rfl]
  have hsum : a + v ≠ 0 := ne_of_gt (add_pos ha hv)
  have hsum' : v + a ≠ 0 := ne_of_gt (add_pos hv ha)
  field_simp
  ring

private lemma tri_quantile (a v q : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    quantile (triangularLaw a v) (1 - q) = min v (a * (1 - q) / q) := by
  let b := a * (1 - q) / q
  have hb0 : 0 ≤ b := div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hq.2.le)) hq.1.le
  have hba : 0 < b + a := by positivity
  have hqb : q * b = a * (1 - q) := by
    dsimp [b]
    field_simp [hq.1.ne']
  have hbCDF : b / (b + a) = 1 - q := by
    apply (div_eq_iff hba.ne').mpr
    nlinarith
  have hx : min v b ∈ {x : ℝ | 0 ≤ x ∧ 1 - q ≤ cdf (triangularLaw a v) x} := by
    refine ⟨le_min hv.le hb0, ?_⟩
    by_cases hvb : v ≤ b
    · rw [min_eq_left hvb, tri_cdf_all a v ha hv]
      simp [triangularCDF, not_lt_of_ge hv.le]
      linarith [hq.1]
    · rw [min_eq_right (le_of_not_ge hvb),
        tri_cdf_interior a v b ha hb0 (lt_of_not_ge hvb), hbCDF]
  unfold quantile
  change sInf {x : ℝ | 0 ≤ x ∧ 1 - q ≤ cdf (triangularLaw a v) x} = min v b
  apply le_antisymm (csInf_le ⟨0, fun _ h => h.1⟩ hx)
  apply le_csInf ⟨_, hx⟩
  rintro p ⟨hp0, hpCDF⟩
  by_cases hvp : v ≤ p
  · exact (min_le_left _ _).trans hvp
  · have hpv : p < v := lt_of_not_ge hvp
    rw [tri_cdf_interior a v p ha hp0 hpv] at hpCDF
    have hpa : 0 < p + a := by positivity
    have hh := (le_div_iff₀ hpa).mp hpCDF
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ hq.1).mpr
    nlinarith

private lemma tri_regular (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    Regular (triangularLaw a v) := by
  have hcurve : ∀ q ∈ Ioo (0 : ℝ) 1,
      revenueQuantile (triangularLaw a v) q = min (v * q) (a * (1 - q)) := by
    intro q hq
    rw [revenueQuantile, tri_quantile a v q ha hv hq,
      mul_min_of_nonneg _ _ hq.1.le]
    congr 1
    · ring
    · field_simp [hq.1.ne']
  have hc : ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun q => min (v * q) (a * (1 - q))) := by
    refine ⟨convex_Ioo 0 1, ?_⟩
    intro x _ y _ r t hr ht hrt
    simp only [smul_eq_mul]
    apply le_min
    · have h1 := mul_le_mul_of_nonneg_left (min_le_left (v * x) (a * (1 - x))) hr
      have h2 := mul_le_mul_of_nonneg_left (min_le_left (v * y) (a * (1 - y))) ht
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left (min_le_right (v * x) (a * (1 - x))) hr
      have h2 := mul_le_mul_of_nonneg_left (min_le_right (v * y) (a * (1 - y))) ht
      nlinarith [congrArg (fun z => a * z) hrt]
  exact hc.congr (fun q hq => (hcurve q hq).symm)

theorem solution (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    ValidMarginal (triangularLaw a v) ∧
    Regular (triangularLaw a v) ∧
    (∀ p : ℝ, rejection (triangularLaw a v) p = triangularReject a v p) ∧
    (∀ p : ℝ, cdf (triangularLaw a v) p = triangularCDF a v p) ∧
    ((triangularLaw a v) {v}).toReal = a / (a + v) ∧
    (∀ᵐ x ∂triangularLaw a v, x ∈ Icc (0 : ℝ) v) := by
  have hs := tri_support a v ha hv
  exact ⟨⟨tri_probability a v, hs.mono (fun _ h => h.1)⟩,
    tri_regular a v ha hv, tri_rejection_all a v ha hv, tri_cdf_all a v ha hv,
    tri_atom a v ha hv, hs⟩

