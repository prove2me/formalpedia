-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_weighted_infimum_interval_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:23:04.862807+00:00
-- url     : https://prove2.me/submissions/a8bbe275-2d7d-47ed-b15a-3ab8da505848

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_weighted_infimum_cdf_scale
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Weighted cumulative measure calculation. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ) (w : ℝ → ℝ), 0 < φ → 0 < q → ν (Iio 0) = 0 →
      (∀ z : ℝ, z < 0 → w z = 0) →
      (∀ z : ℝ, 0 ≤ w z) →
      ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → cdf ν b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ a b : ℝ, a ≤ b →
      (∫⁻ z in Ioc a b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (q / φ *
        (Real.exp (-φ * b) * w b - Real.exp (-φ * a) * w a)) := by
  intro ν hν φ q w hφ hq hsupp hzero hnonneg hcont hcdf a b hab
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-φ * z))
  have hcum := p2m88_weighted_infimum_cdf_scale ν φ q w
    hφ hq hsupp hzero hnonneg hcont hcdf
  have hset : Ioc a b ∪ Iic a = Iic b := by
    rw [union_comm, Iic_union_Ioc_eq_Iic hab]
  have hd : Disjoint (Ioc a b) (Iic a) := by
    apply Set.disjoint_left.mpr
    intro z hz hza
    exact not_lt_of_ge hza hz.1
  have hsum : (∫⁻ z in Iic b, f z ∂ν) =
      (∫⁻ z in Ioc a b, f z ∂ν) + (∫⁻ z in Iic a, f z ∂ν) := by
    rw [← hset, Measure.restrict_union hd measurableSet_Iic, lintegral_add_measure]
  change (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) = _ at hsum
  have ha := hcum a
  change (∫⁻ z in Iic a, f z ∂ν) = _ at ha
  rw [hcum b, ha] at hsum
  have hdif := ENNReal.sub_eq_of_eq_add ENNReal.ofReal_ne_top hsum
  change (∫⁻ z in Ioc a b, f z ∂ν) = _
  rw [← hdif, ← ENNReal.ofReal_sub _ (mul_nonneg (mul_nonneg (div_nonneg hq.le hφ.le) (Real.exp_pos _).le) (hnonneg a))]
  congr 1
  ring
