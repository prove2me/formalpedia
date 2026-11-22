-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T02:37:15.907262+00:00
-- url     : https://prove2.me/submissions/65c672e4-1180-4b4f-9904-2838fb947aef

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupp : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≤ 1 := by
  have hae : ∀ᵐ y ∂μ, 0 ≤ y := by
    rw [MeasureTheory.ae_iff]
    have hset : {a | ¬0 ≤ a} = Iio (0 : ℝ) := by ext a; simp [not_le]
    rw [hset]; exact hsupp
  have h1 : ∀ᵐ y ∂μ, ENNReal.ofReal (Real.exp (-1 * y)) ≤ 1 := by
    filter_upwards [hae] with y hy
    rw [ENNReal.ofReal_le_one, Real.exp_le_one_iff]; linarith
  calc (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂μ) ≤ ∫⁻ _ : ℝ, 1 ∂μ :=
        MeasureTheory.lintegral_mono_ae h1
    _ = μ Set.univ := MeasureTheory.lintegral_one
    _ = 1 := MeasureTheory.IsProbabilityMeasure.measure_univ
