-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-22T03:27:40.805634+00:00
-- url     : https://prove2.me/submissions/5696ccff-962d-45bd-80f7-4c712d8ceaa9

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Probability_Progressive_F000
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open LevyStochCalc

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {H : Ω → ℝ → ℝ}
    (hp : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => Set.indicator (Set.Icc (0 : ℝ) T) (H ω) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  let S : Set (Ω × ℝ) := Prod.snd ⁻¹' Set.Icc (0 : ℝ) T
  have hS : MeasurableSet S := measurable_snd measurableSet_Icc
  have h := (hp t).indicator hS
  convert h using 1
  funext p
  by_cases h₁ : p.2 ≤ t <;> by_cases h₂ : 0 ≤ p.2 ∧ p.2 ≤ T <;>
    simp [S, Set.indicator_apply, h₁, h₂]
