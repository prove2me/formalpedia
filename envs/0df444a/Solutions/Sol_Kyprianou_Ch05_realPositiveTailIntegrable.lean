-- Prove2me | solution 1 for Kyprianou.Ch05.realPositiveTailIntegrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:44.871274+00:00
-- url     : https://prove2.me/submissions/60541fbd-672c-4b37-8b46-e695262b6697
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_real_integrable_of_finite_firstMoment
import Theorems.Thm_Kyprianou_Ch05_realToNNRealPositiveTailTransport
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Transfer the proved nonnegative-real first-moment tail estimate to real measures. -/
theorem solution (F : Measure Real) [IsProbabilityMeasure F]
    (hInt : Integrable (fun z : Real => z) F) :
    IntegrableOn (fun t : Real => (F (Ioi t)).toReal) (Ioi (0 : Real)) := by
  obtain ⟨hfirst,he⟩ := realToNNRealPositiveTailTransport F hInt
  have hi := AvramDividend.Classical.positive_jump_tail_real_integrable_of_finite_firstMoment _ hfirst
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact congrArg ENNReal.toReal (he t ht)
