-- Prove2me | solution 1 for Kyprianou.Ch05.completionMapEqOfAEMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:28.509344+00:00
-- url     : https://prove2.me/submissions/ba87584b-2b19-4bb1-a76b-5294897560a6

import Mathlib.Probability.ConditionalProbability
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega B : Type} [MeasurableSpace Omega] [MeasurableSpace B]
    (P : Measure Omega) (f : Omega → B) (hf : AEMeasurable f P) :
    Measure.map (fun w : NullMeasurableSpace Omega P => f w) P.completion =
      Measure.map f P := by
  have hc : Measurable (fun w : NullMeasurableSpace Omega P => f w) :=
    hf.nullMeasurable.measurable'
  ext s hs
  rw [Measure.map_apply hc hs, Measure.map_apply_of_aemeasurable hf hs]
  rfl
