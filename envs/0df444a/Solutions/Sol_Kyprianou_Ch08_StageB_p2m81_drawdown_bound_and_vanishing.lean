-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_bound_and_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T01:39:12.427618+00:00
-- url     : https://prove2.me/submissions/4b0799f6-9e46-4f73-97a8-71a0e03c976c

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap_and_ratio_bound
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_family_vanishing
open MeasureTheory ProbabilityTheory Filter Set Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
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
          f d * (1 - s / d)) :
    (∀ d : ℝ, 1 ≤ d → d / f d ≤ 1 / f 1) ∧
    (∀ x : ℝ, 0 < x →
      Tendsto (fun d : ℝ => (ρd d) {x}) atTop (nhds (0 : ℝ≥0∞))) := by
  classical
  obtain ⟨-, -, hbound⟩ :=
    Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap_and_ratio_bound f hpos hdraw ρd hρd
  refine ⟨hbound, fun x hx => ?_⟩
  exact Kyprianou.Ch08.StageB.p2m81_drawdown_family_vanishing f hpos hdraw ρd hρd x hx
