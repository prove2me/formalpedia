-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_truncated_exponential_cdf_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:40:09.0581+00:00
-- url     : https://prove2.me/submissions/d688778b-1529-4dd5-9f5e-c66982719e82

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_cdf_truncated_tonelli
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08.StageB
/-- Truncated cumulative Laplace calculation. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ b : ℝ), 0 < φ → 0 ≤ b → ν (Iio 0) = 0 →
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ * z)) ∂ν) =
      ENNReal.ofReal (Real.exp (-φ * b) * cdf ν b +
        φ * ∫ t in (0 : ℝ)..b, Real.exp (-φ * t) * cdf ν t) := by
  intro ν hν φ b hφ hb hsupp
  rw [p2m88_cdf_truncated_tonelli ν φ b hφ hb hsupp]
  let Q : Measure ℝ := volume.restrict (Ioc (0 : ℝ) b)
  let g : ℝ → ℝ := fun t => Real.exp (-φ*t) * cdf ν t
  have hm : Measurable g :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      (monotone_cdf (μ := ν)).measurable
  have hi : Integrable g Q := by
    have hExp : Integrable (fun t : ℝ => Real.exp (-φ*t)) Q :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable
        (μ := volume) 0 b).1
    apply hExp.mono' hm.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (cdf_nonneg ν t))]
    simpa using mul_le_mul_of_nonneg_left (cdf_le_one (μ := ν) t) (Real.exp_pos _).le
  have hn : ∀ᵐ t ∂Q, 0 ≤ g t :=
    Filter.Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (cdf_nonneg ν t)
  have hg : ENNReal.ofReal (∫ t in (0 : ℝ)..b, g t) =
      ∫⁻ t in Ioc 0 b, ENNReal.ofReal (Real.exp (-φ*t)) * ν (Iic t) := by
    rw [intervalIntegral.integral_of_le hb, ofReal_integral_eq_lintegral_ofReal hi hn]
    apply lintegral_congr
    intro t
    rw [show g t = Real.exp (-φ*t)*cdf ν t from rfl, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ofReal_cdf]
  rw [← hg, ← ofReal_cdf ν b, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul hφ.le, ← ENNReal.ofReal_add
      (mul_nonneg (Real.exp_pos _).le (cdf_nonneg ν b))
      (mul_nonneg hφ.le (by
        rw [intervalIntegral.integral_of_le hb]
        exact integral_nonneg_of_ae hn))]
