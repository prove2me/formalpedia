-- Prove2me | solution 1 for LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:00:46.829336+00:00
-- url     : https://prove2.me/submissions/a093271b-4861-49c5-a0de-0904ca9fe6d6

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F001

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)
      = ENNReal.ofReal (φ.partition i.succ - φ.partition i.castSucc) * ν (φ.A i) := by
  rw [SimplePredictable.fullRect, LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod]
  congr 1
  have h0 : 0 ≤ φ.partition i.castSucc := by
    rw [← φ.partition_zero]
    exact φ.partition_strictMono.monotone (Fin.zero_le _)
  have hsub : Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ⊆ Set.Ici (0 : ℝ) := by
    intro t ht
    exact h0.trans ht.1.le
  rw [Measure.restrict_apply' measurableSet_Ici, Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
