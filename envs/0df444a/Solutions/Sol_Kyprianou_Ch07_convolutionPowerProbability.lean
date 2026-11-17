-- Prove2me | solution 1 for Kyprianou.Ch07.convolutionPowerProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:32:34.273308+00:00
-- url     : https://prove2.me/submissions/ad49c126-d13b-42f6-a8f8-a25dedae223e

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G] (n : Nat) :
    IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) := by
  induction n with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac (0 : Real))
    infer_instance
  | succ n ih =>
    change IsProbabilityMeasure
      (Measure.map (fun z : Real × Real => z.1 + z.2)
        ((Kyprianou.Ch07.convolutionPower G n).prod G))
    letI : IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) := ih
    have hProd : IsProbabilityMeasure
        ((Kyprianou.Ch07.convolutionPower G n).prod G) := by
      infer_instance
    exact Measure.isProbabilityMeasure_map
      ((measurable_fst.add measurable_snd).aemeasurable)
