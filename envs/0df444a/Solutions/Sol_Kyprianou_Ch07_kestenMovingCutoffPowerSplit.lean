-- Prove2me | solution 1 for Kyprianou.Ch07.kestenMovingCutoffPowerSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:53:59.471744+00:00
-- url     : https://prove2.me/submissions/85c4b3c1-d323-48bb-8fb9-67033a6b8eca

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionComm
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailSplitAtLe
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (n : Nat) (x T : Real) :
    (Kyprianou.Ch07.convolutionPower G (n + 1)) (Set.Ioi x) ≤
      G (Set.Ioi (x - T)) +
        ∫⁻ a : Real in Set.Iic (x - T),
          (Kyprianou.Ch07.convolutionPower G n)
            (Set.Ioi (x - a)) ∂G := by
  letI : IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) :=
    Kyprianou.Ch07.convolutionPowerProbability G n
  change (Kyprianou.Ch07.sumConvolution
    (Kyprianou.Ch07.convolutionPower G n) G) (Set.Ioi x) ≤ _
  rw [Kyprianou.Ch07.sumConvolutionComm]
  exact Kyprianou.Ch07.sumConvolutionTailSplitAtLe
    G (Kyprianou.Ch07.convolutionPower G n) x (x - T)
