-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_step_lt
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:24:11.605629+00:00
-- url     : https://prove2.me/submissions/38feb522-149a-49de-8f8b-0069fb0739f9

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (hdraw : ∀ d : ℝ, 0 < d → ∃ ρ : Measure ℝ,
      IsProbabilityMeasure ρ ∧ ρ (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
          f d * (1 - s / d))
    (ρd : ℝ → Measure ℝ)
    (hρd : ∀ d : ℝ, 0 < d →
      IsProbabilityMeasure (ρd d) ∧ (ρd d) (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(ρd d)).toReal =
          f d * (1 - s / d))
    (d : ℝ) (hd1 : 1 < d) : f 1 < f d := by
  have hd : 0 < d := by linarith
  have he := (hρd d hd).2.2 1 (by norm_num)
  by_contra! h
  have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h)
    (ENNReal.toReal_nonneg (a := ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)))
  have hright : 0 < f d * (1 - 1 / d) := by
    apply mul_pos (hpos d hd)
    exact sub_pos.mpr ((div_lt_iff₀ hd).mpr (by linarith))
  linarith
