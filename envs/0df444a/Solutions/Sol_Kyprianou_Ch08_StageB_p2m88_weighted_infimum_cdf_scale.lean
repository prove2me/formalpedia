-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_weighted_infimum_cdf_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:08:36.276047+00:00
-- url     : https://prove2.me/submissions/0ec42c1a-4374-4c03-bfb4-6db0be092376

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_truncated_exponential_cdf_identity
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_primitive_exp_cdf_calculus
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
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
      ∀ b : ℝ,
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (q / φ * Real.exp (-φ * b) * w b) := by
  intro ν hν φ q w hφ hq hsupp hzero hnonneg hcont hcdf b
  by_cases hb : 0 ≤ b
  · rw [p2m88_truncated_exponential_cdf_identity ν φ b hφ hb hsupp]
    exact congrArg ENNReal.ofReal
      (p2m88_primitive_exp_cdf_calculus φ q w (cdf ν) hφ hq hcont hcdf b hb)
  · have hnull : ν (Iic b) = 0 := measure_mono_null
        (show Iic b ⊆ Iio 0 from fun z hz => lt_of_le_of_lt hz (lt_of_not_ge hb)) hsupp
    rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure,
      hzero b (lt_of_not_ge hb), mul_zero, ENNReal.ofReal_zero]
