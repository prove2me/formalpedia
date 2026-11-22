-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_singleton_tendsto_zero_public
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T04:01:20.062661+00:00
-- url     : https://prove2.me/submissions/f917e882-108f-446f-b17f-fb899f49b407

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_family_vanishing
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
    (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun d : ℝ =>
        ((if hd : 0 < d then Classical.choose (hdraw d hd) else 0) : Measure ℝ) ({x} : Set ℝ))
      atTop (nhds (0 : ENNReal)) := by
  classical
  let μ (d : ℝ) : Measure ℝ := if hd : 0 < d then Classical.choose (hdraw d hd) else 0
  have hμ (d : ℝ) (hd : 0 < d) :
      IsProbabilityMeasure (μ d) ∧ (μ d) (Iio (0 : ℝ)) = 0 ∧
      ∀ s : ℝ, 0 < s →
        (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂(μ d)).toReal =
          f d * (1 - s / d) := by
    simpa only [μ, dif_pos hd] using Classical.choose_spec (hdraw d hd)
  exact Kyprianou.Ch08.StageB.p2m81_drawdown_family_vanishing f hpos hdraw μ hμ x hx
