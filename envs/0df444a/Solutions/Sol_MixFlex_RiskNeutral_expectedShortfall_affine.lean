-- Prove2me | solution 1 for MixFlex.RiskNeutral.expectedShortfall_affine
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:47:08.231983+00:00
-- url     : https://prove2.me/submissions/5066415e-313e-4ffb-9ab1-f95829ed16a1

import Definitions.Def_MixFlex_RiskNeutral_Model
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MixFlex.RiskNeutral
noncomputable section
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

private theorem quantile_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (a b : ℝ) (ha : 0 < a)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    lowerQuantile μ (fun ω => a*Z ω+b) α = a*lowerQuantile μ Z α+b := by
  have ham : Measurable (fun ω => a*Z ω+b) := (hm.const_mul a).add_const b
  have hset (t : ℝ) : {ω | a*Z ω+b ≤ a*t+b} = {ω | Z ω ≤ t} := by
    ext ω; simp only [mem_setOf_eq, add_le_add_iff_right, mul_le_mul_iff_right₀ ha]
  have hq := (quantile_iff μ Z hm α hα0 hα1 (lowerQuantile μ Z α)).mp le_rfl
  apply le_antisymm
  · apply (quantile_iff μ _ ham α hα0 hα1 _).mpr
    simpa only [hset] using hq
  · have hqa := (quantile_iff μ _ ham α hα0 hα1 (lowerQuantile μ (fun ω => a*Z ω+b) α)).mp le_rfl
    let t := (lowerQuantile μ (fun ω => a*Z ω+b) α-b)/a
    have ht : a*t+b = lowerQuantile μ (fun ω => a*Z ω+b) α := by
      dsimp [t]; field_simp; ring
    rw [← ht, hset] at hqa
    have h := (quantile_iff μ Z hm α hα0 hα1 t).mpr hqa
    nlinarith

private theorem truncated_integral_affine {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hm : Measurable Z) (hi : Integrable Z μ)
    (a b q : ℝ) :
    (∫ ω, (a*Z ω+b)*(if Z ω≤q then 1 else 0) ∂μ) =
      a*(∫ ω, Z ω*(if Z ω≤q then 1 else 0) ∂μ)+b*μ.real {ω|Z ω≤q} := by
  have hs : MeasurableSet {ω | Z ω≤q} := measurableSet_le hm measurable_const
  have ht : Integrable (fun ω => Z ω*(if Z ω≤q then 1 else 0)) μ := by
    convert! hi.indicator hs using 1
    funext ω
    by_cases h : Z ω≤q <;> simp [Set.indicator,h]
  have h1 : Integrable (fun ω => if Z ω≤q then (1:ℝ) else 0) μ := by
    convert! (integrable_const (μ:=μ) (1:ℝ)).indicator hs using 1
  have hval : (∫ ω, (if Z ω≤q then (1:ℝ) else 0) ∂μ) = μ.real {ω | Z ω≤q} := by
    simpa only [Set.indicator,mem_setOf_eq,smul_eq_mul,mul_one] using
      (integral_indicator_const (μ:=μ) (1:ℝ) hs)
  calc
    _ = ∫ ω, a*(Z ω*(if Z ω≤q then 1 else 0))+b*(if Z ω≤q then 1 else 0) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = _ := by rw [integral_add (ht.const_mul a) (h1.const_mul b),
      integral_const_mul,integral_const_mul,hval]

 theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hmeas : Measurable Z) (hint : Integrable Z μ)
    (a b : ℝ) (ha : 0 < a) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    expectedShortfall μ (fun ω => a * Z ω + b) α = a * expectedShortfall μ Z α - b := by
  have hq := quantile_affine μ Z hmeas a b ha α hα0 hα1
  let q := lowerQuantile μ Z α
  have hle (ω : Ω) : a*Z ω+b ≤ a*q+b ↔ Z ω≤q := by
    simp only [add_le_add_iff_right,mul_le_mul_iff_right₀ ha]
  unfold expectedShortfall
  rw [hq]
  change -(1/α)*((∫ ω,(a*Z ω+b)*(if a*Z ω+b≤a*q+b then 1 else 0) ∂μ)+
    (a*q+b)*(α-μ.real {ω|a*Z ω+b≤a*q+b})) =
    a*(-(1/α)*((∫ ω,Z ω*(if Z ω≤q then 1 else 0) ∂μ)+q*(α-μ.real {ω|Z ω≤q})))-b
  simp only [hle]
  rw [truncated_integral_affine μ Z hmeas hint a b q]
  field_simp
  ring
