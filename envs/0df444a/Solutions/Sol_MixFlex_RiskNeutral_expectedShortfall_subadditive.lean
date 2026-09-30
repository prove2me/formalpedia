-- Prove2me | solution 1 for MixFlex.RiskNeutral.expectedShortfall_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:51:06.36727+00:00
-- url     : https://prove2.me/submissions/142545db-9d8f-4347-b467-8bada59d62e2

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MixFlex.RiskNeutral
noncomputable section
attribute [local instance] Classical.propDecidable
private theorem quantile_iff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    lowerQuantile μ Z α ≤ t ↔ α ≤ μ.real {ω | Z ω ≤ t} := by
  haveI : IsProbabilityMeasure (μ.map Z) := μ.isProbabilityMeasure_map hm.aemeasurable
  let F := cdf (μ.map Z)
  have hf (y : ℝ) : F y = μ.real {ω | Z ω ≤ y} := by
    rw [cdf_eq_real]
    change ((μ.map Z) (Iic y)).toReal = (μ (Z ⁻¹' Iic y)).toReal
    rw [Measure.map_apply hm measurableSet_Iic]
  have heq : {y : ℝ | α ≤ μ.real {ω | Z ω ≤ y}} = {y : ℝ | α ≤ F y} := by
    ext y; simp only [Set.mem_setOf_eq, hf]
  let S := {y : ℝ | α ≤ F y}
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop (μ.map Z)).eventually (eventually_gt_nhds hα1)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (μ.map Z)).eventually (eventually_lt_nhds hα0)).exists
    refine ⟨y, fun z hz => ?_⟩
    by_contra h
    have hh := F.mono (le_of_not_ge h)
    exact (not_lt_of_ge (hz.trans hh)) hy
  have hmem : α ≤ F (sInf S) := by
    have hlim : Tendsto F (𝓝[>] sInf S) (𝓝 (F (sInf S))) :=
      (F.right_continuous _).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact hz.trans (F.mono hzy.le)
  rw [← hf, lowerQuantile, heq]
  exact ⟨fun h => hmem.trans (F.mono h), fun h => csInf_le hb h⟩

private theorem quantile_left {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    μ.real {ω | Z ω < lowerQuantile μ Z α} ≤ α := by
  haveI : IsProbabilityMeasure (μ.map Z) := μ.isProbabilityMeasure_map hm.aemeasurable
  let F := cdf (μ.map Z)
  let q := lowerQuantile μ Z α
  have hf (y : ℝ) : F y = μ.real {ω | Z ω ≤ y} := by
    rw [cdf_eq_real]
    change ((μ.map Z) (Iic y)).toReal = (μ (Z ⁻¹' Iic y)).toReal
    rw [Measure.map_apply hm measurableSet_Iic]
  have hlim := F.mono.tendsto_leftLim q
  have hl0 : 0 ≤ Function.leftLim F q := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall (fun t => cdf_nonneg _ _)
  have hl : Function.leftLim F q ≤ α := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply le_of_lt
    by_contra! h
    have hqt := (quantile_iff μ Z hm α hα0 hα1 t).mpr (by rwa [← hf])
    exact (not_lt_of_ge hqt) ht
  change (μ (Z ⁻¹' Iio q)).toReal ≤ α
  rw [← Measure.map_apply hm measurableSet_Iio,← measure_cdf (μ.map Z)]
  rw [StieltjesFunction.measure_Iio _ (tendsto_cdf_atBot _),sub_zero,
    ENNReal.toReal_ofReal hl0]
  exact hl

private theorem indicator_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s) :
    Integrable (fun ω => if ω∈s then (1:ℝ) else 0) μ ∧
    (∫ ω, (if ω∈s then (1:ℝ) else 0) ∂μ) = μ.real s := by
  constructor
  · convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  · simpa only [Set.indicator,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)

private theorem hinge_int {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (t : ℝ) :
    (∫ ω, max (t-Z ω) 0 ∂μ) = t*μ.real {ω|Z ω≤t} -
      (∫ ω,Z ω*(if Z ω≤t then 1 else 0) ∂μ) := by
  have hs : MeasurableSet {ω | Z ω≤t} := measurableSet_le hm measurable_const
  have ht : Integrable (fun ω => Z ω*(if Z ω≤t then 1 else 0)) μ := by
    convert! hi.indicator hs using 1
    funext ω
    by_cases h : Z ω≤t <;> simp [Set.indicator,h]
  obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω≤t} hs
  simp only [Set.mem_setOf_eq] at h1 hval
  calc
    _ = ∫ ω,t*(if Z ω≤t then 1 else 0)-Z ω*(if Z ω≤t then 1 else 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases h : Z ω≤t
      · simp only [h,ite_true,mul_one,max_eq_left (sub_nonneg.mpr h)]
      · simp only [h,ite_false,mul_zero,sub_zero,max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
    _ = _ := by rw [integral_sub (h1.const_mul t) ht,integral_const_mul,hval]

private theorem es_hinge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (α : ℝ) (hα0 : 0 < α) :
    expectedShortfall μ Z α = -lowerQuantile μ Z α +
      (∫ ω,max (lowerQuantile μ Z α-Z ω) 0 ∂μ)/α := by
  rw [hinge_int μ Z hm hi]
  unfold expectedShortfall
  field_simp
  ring

private theorem es_le_hinge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) :
    expectedShortfall μ Z α ≤ -t+(∫ ω,max (t-Z ω) 0 ∂μ)/α := by
  let q := lowerQuantile μ Z α
  have hiq : Integrable (fun ω=>max (q-Z ω) 0) μ :=
    ((integrable_const q).sub hi).sup (integrable_const 0)
  have hit : Integrable (fun ω=>max (t-Z ω) 0) μ :=
    ((integrable_const t).sub hi).sup (integrable_const 0)
  rw [es_hinge μ Z hm hi α hα0]
  change -q+(∫ ω,max (q-Z ω) 0 ∂μ)/α ≤ -t+(∫ ω,max (t-Z ω) 0 ∂μ)/α
  by_cases hqt : q≤t
  · obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω≤q} (measurableSet_le hm measurable_const)
    simp only [Set.mem_setOf_eq] at h1 hval
    have hp : ∀ ω, max (q-Z ω) 0+(t-q)*(if Z ω≤q then 1 else 0) ≤ max (t-Z ω) 0 := by
      intro ω
      simp only [max_def]
      split_ifs <;> linarith
    have hh := integral_mono_ae (hiq.add (h1.const_mul (t-q))) hit (Eventually.of_forall hp)
    rw [integral_add' hiq (h1.const_mul (t-q)),integral_const_mul,hval] at hh
    have hq := (quantile_iff μ Z hm α hα0 hα1 q).mp le_rfl
    have hm := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hqt)
    apply (mul_le_mul_iff_right₀ hα0).mp
    field_simp
    nlinarith
  · obtain ⟨h1,hval⟩ := indicator_int μ {ω|Z ω<q} (measurableSet_lt hm measurable_const)
    simp only [Set.mem_setOf_eq] at h1 hval
    have hp : ∀ ω, max (q-Z ω) 0+(t-q)*(if Z ω<q then 1 else 0) ≤ max (t-Z ω) 0 := by
      intro ω
      simp only [max_def]
      split_ifs <;> linarith
    have hh := integral_mono_ae (hiq.add (h1.const_mul (t-q))) hit (Eventually.of_forall hp)
    rw [integral_add' hiq (h1.const_mul (t-q)),integral_const_mul,hval] at hh
    have hq := quantile_left μ Z hm α hα0 hα1
    have hm := mul_le_mul_of_nonpos_left hq (sub_nonpos.mpr (le_of_not_ge hqt))
    apply (mul_le_mul_iff_right₀ hα0).mp
    field_simp
    nlinarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (Z : Fin N → Ω → ℝ) (hmeas : ∀ n, Measurable (Z n))
    (hint : ∀ n, Integrable (Z n) μ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    expectedShortfall μ (fun ω => ∑ n, Z n ω) α ≤ ∑ n, expectedShortfall μ (Z n) α := by
  let q : Fin N → ℝ := fun n=>lowerQuantile μ (Z n) α
  have hms : Measurable (fun ω=>∑ n,Z n ω) := Finset.measurable_sum _ (fun n _=>hmeas n)
  have his : Integrable (fun ω=>∑ n,Z n ω) μ := integrable_finset_sum _ (fun n _=>hint n)
  have hih (n : Fin N) : Integrable (fun ω=>max (q n-Z n ω) 0) μ :=
    ((integrable_const (q n)).sub (hint n)).sup (integrable_const 0)
  have hihs : Integrable (fun ω=>max ((∑ n,q n)-(∑ n,Z n ω)) 0) μ :=
    ((integrable_const _).sub his).sup (integrable_const 0)
  have hineq : (∫ ω,max ((∑ n,q n)-(∑ n,Z n ω)) 0 ∂μ) ≤
      ∑ n,∫ ω,max (q n-Z n ω) 0 ∂μ := by
    rw [← integral_finset_sum _ (fun n _=>hih n)]
    apply integral_mono_ae hihs (integrable_finset_sum _ (fun n _=>hih n))
    filter_upwards [] with ω
    apply max_le
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun n _=>le_max_left _ _)
    · exact Finset.sum_nonneg (fun n _=>le_max_right _ _)
  calc
    _ ≤ -(∑ n,q n)+(∫ ω,max ((∑ n,q n)-(∑ n,Z n ω)) 0 ∂μ)/α :=
      es_le_hinge μ _ hms his α hα0 hα1 _
    _ ≤ -(∑ n,q n)+(∑ n,∫ ω,max (q n-Z n ω) 0 ∂μ)/α := by gcongr
    _ = _ := by
      simp_rw [es_hinge μ _ (hmeas _) (hint _) α hα0]
      simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,Finset.sum_div]
      rfl
