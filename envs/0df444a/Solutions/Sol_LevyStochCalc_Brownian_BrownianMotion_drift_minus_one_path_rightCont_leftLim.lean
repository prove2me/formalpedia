-- Prove2me | solution 1 for LevyStochCalc.Brownian.BrownianMotion.drift_minus_one_path_rightCont_leftLim
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:00:53.801164+00:00
-- url     : https://prove2.me/submissions/6bb32dab-be52-4acb-95c8-9be974dde889

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Mathlib.Tactic

open MeasureTheory Filter Set Topology
open scoped NNReal
open LevyStochCalc.Brownian
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (W : BrownianMotion P)
    (ω : Ω) (hpath : Continuous (fun t : ℝ => W.W t ω)) :
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (Ici t) t) ∧
    (∀ t : ℝ≥0, 0 < t → ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) (𝓝[<] t) (𝓝 l)) := by
  have hc : Continuous (fun s : ℝ≥0 => W.W (s : ℝ) ω - (s : ℝ)) :=
    (hpath.comp NNReal.continuous_coe).sub NNReal.continuous_coe
  exact ⟨fun t => hc.continuousAt.continuousWithinAt,
    fun t _ => ⟨_, hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
