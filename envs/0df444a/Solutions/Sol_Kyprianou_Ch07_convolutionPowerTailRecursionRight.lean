-- Prove2me | solution 1 for Kyprianou.Ch07.convolutionPowerTailRecursionRight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:29:15.478093+00:00
-- url     : https://prove2.me/submissions/0c0e5fda-9c4d-4b48-aea3-94bd5673c31c

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Theorems.Thm_Kyprianou_Ch07_convolutionPowerProbability
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionComm
import Theorems.Thm_Kyprianou_Ch07_sumConvolutionTailIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G] (n : Nat) (x : Real) :
    (Kyprianou.Ch07.convolutionPower G (n + 1)) (Set.Ioi x) =
      ∫⁻ a : Real, (Kyprianou.Ch07.convolutionPower G n)
        (Set.Ioi (x - a)) ∂G := by
  letI : IsProbabilityMeasure (Kyprianou.Ch07.convolutionPower G n) :=
    Kyprianou.Ch07.convolutionPowerProbability G n
  change (Kyprianou.Ch07.sumConvolution
    (Kyprianou.Ch07.convolutionPower G n) G) (Set.Ioi x) =
      ∫⁻ a : Real, (Kyprianou.Ch07.convolutionPower G n)
        (Set.Ioi (x - a)) ∂G
  rw [Kyprianou.Ch07.sumConvolutionComm]
  exact Kyprianou.Ch07.sumConvolutionTailIntegral
    G (Kyprianou.Ch07.convolutionPower G n) x
