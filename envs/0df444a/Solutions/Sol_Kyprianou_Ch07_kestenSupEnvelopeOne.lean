-- Prove2me | solution 1 for Kyprianou.Ch07.kestenSupEnvelopeOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:36:45.157204+00:00
-- url     : https://prove2.me/submissions/1189e901-9f1c-46af-ba69-b87d50c2bf96

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenSupRatioBounded
import Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x)) :
    Kyprianou.Ch07.kestenSupEnvelope G 1 = 1 := by
  have hBound (x : Real) (hx : 0 < x) :
      ((Kyprianou.Ch07.convolutionPower G 1) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal ≤ 1 := by
    rw [Kyprianou.Ch07.kestenOnefoldTailRatio G hPositiveTail x hx]
  have hSup := Kyprianou.Ch07.kestenSupRatioBounded
    G 1 1 hBound 1 (by norm_num)
  have hLeft : (1 : Real) ≤ Kyprianou.Ch07.kestenSupEnvelope G 1 := by
    have heq := Kyprianou.Ch07.kestenOnefoldTailRatio
      G hPositiveTail 1 (by norm_num)
    simpa [Kyprianou.Ch07.kestenSupEnvelope, heq] using hSup.1
  have hRight : Kyprianou.Ch07.kestenSupEnvelope G 1 ≤ 1 := by
    simpa only [Kyprianou.Ch07.kestenSupEnvelope] using hSup.2
  exact le_antisymm hRight hLeft
