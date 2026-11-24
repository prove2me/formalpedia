-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_cdf_truncated_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:39:48.216558+00:00
-- url     : https://prove2.me/submissions/f2ace1a8-52ba-4b81-b81f-4c3559f838f6

import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_restricted_cdf_laplace_split
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
      (∫⁻ z in Iic b, ENNReal.ofReal (Real.exp (-φ*z)) ∂ν) =
      ENNReal.ofReal (Real.exp (-φ*b)) * ν (Iic b) +
        ENNReal.ofReal φ *
          (∫⁻ t in Ioc 0 b, ENNReal.ofReal (Real.exp (-φ*t)) * ν (Iic t)) := by
  intro ν hν φ b hφ hb hsupp
  let β := ν.restrict (Iic b)
  have hβ : β (Iio 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iio]
    exact measure_mono_null Set.inter_subset_left hsupp
  have h := AvramDividend.Classical.positiveLaplace_cumulative_measure β φ hφ hβ
  change (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-φ*t)) *
    (ν.restrict (Iic b)) (Iic t)) = _ at h
  rw [p2m88_restricted_cdf_laplace_split ν φ b hφ hb] at h
  have hinv : ENNReal.ofReal (1 / φ) = (ENNReal.ofReal φ)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hφ, ENNReal.ofReal_one, one_div]
  rw [hinv] at h
  have hcancel : ENNReal.ofReal φ * (ENNReal.ofReal φ)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp [hφ]) ENNReal.ofReal_ne_top
  have htail : ENNReal.ofReal φ *
      (ENNReal.ofReal (Real.exp (-φ*b) / φ) * ν (Iic b)) =
      ENNReal.ofReal (Real.exp (-φ*b)) * ν (Iic b) := by
    rw [ENNReal.ofReal_div_of_pos hφ, ENNReal.div_eq_inv_mul, ← mul_assoc,
      ← mul_assoc, hcancel, one_mul]
  have hc := congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal φ * z) h
  change ENNReal.ofReal φ * (_ + _) =
    ENNReal.ofReal φ * ((ENNReal.ofReal φ)⁻¹ * _) at hc
  rw [mul_add, htail, ← mul_assoc (ENNReal.ofReal φ) (ENNReal.ofReal φ)⁻¹,
    hcancel, one_mul, add_comm] at hc
  exact hc.symm
