-- Prove2me | solution 1 for Kyprianou.Ch07.convolutionPowerTailLeOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:42:16.674201+00:00
-- url     : https://prove2.me/submissions/a05d18a6-03d8-4e50-894d-cc28f9cb7816

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (n : Nat) (x : Real) :
    ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal ≤ 1 := by
  letI : IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) :=
    Kyprianou.Ch07.convolutionPowerProbability G n
  have hm : (Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x) ≤ 1 :=
    prob_le_one
  have h := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) hm
  simpa only [ENNReal.toReal_one] using h
