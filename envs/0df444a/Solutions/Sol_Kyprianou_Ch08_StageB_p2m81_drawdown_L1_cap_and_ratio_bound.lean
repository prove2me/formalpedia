-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap_and_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T02:29:40.965912+00:00
-- url     : https://prove2.me/submissions/81be486a-33d4-4695-9526-25827b546751

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_L1_cap
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_l1_bounds
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_step_lt
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_drawdown_ratio_bound
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
    (∀ d : ℝ, 0 < d →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)) ≤ 1 ∧
      0 < ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) ∧
      ((∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y)) ∂(ρd d)).toReal) ≤ 1) ∧
    (∀ d : ℝ, 1 < d → f 1 < f d) ∧
    (∀ d : ℝ, 1 ≤ d → d / f d ≤ 1 / f 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨hprob, hsupp_d, _⟩ := hρd d hd; haveI := hprob
    exact ⟨Kyprianou.Ch08.StageB.p2m81_drawdown_L1_cap (ρd d) hsupp_d,
      Kyprianou.Ch08.StageB.p2m81_drawdown_l1_bounds (ρd d) hsupp_d⟩
  · intro d hd1
    exact Kyprianou.Ch08.StageB.p2m81_drawdown_step_lt f hpos hdraw ρd hρd d hd1
  · intro d hd1
    exact Kyprianou.Ch08.StageB.p2m81_drawdown_ratio_bound f hpos hdraw ρd hρd d hd1
