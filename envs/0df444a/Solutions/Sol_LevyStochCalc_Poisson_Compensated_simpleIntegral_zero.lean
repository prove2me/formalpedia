-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.simpleIntegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:51:38.390225+00:00
-- url     : https://prove2.me/submissions/a1bf42fe-d799-4ede-bfed-130e714dcc07

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    simpleIntegral N φ 0 ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : (0 : ℝ) ≤ φ.partition i.castSucc := by
    rw [← φ.partition_zero]
    exact φ.partition_strictMono.monotone (Fin.zero_le _)
  have h1 : (0 : ℝ) ≤ φ.partition i.succ := by
    rw [← φ.partition_zero]
    exact φ.partition_strictMono.monotone (Fin.zero_le _)
  have hrect : φ.timeRect i 0 = ∅ := by
    simp [SimplePredictable.timeRect, min_eq_right h0, min_eq_right h1]
  simp [hrect, LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
