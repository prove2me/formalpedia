-- Prove2me | solution 1 for Kyprianou.Ch07.convolutionPowerTailRecursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:26:27.088997+00:00
-- url     : https://prove2.me/submissions/6a8179d7-5ab7-4d7a-9a8d-351ebadff87e

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
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
      ∫⁻ a : Real, G (Set.Ioi (x - a))
        ∂(Kyprianou.Ch07.convolutionPower G n) := by
  change (Kyprianou.Ch07.sumConvolution
    (Kyprianou.Ch07.convolutionPower G n) G) (Set.Ioi x) =
      ∫⁻ a : Real, G (Set.Ioi (x - a))
        ∂(Kyprianou.Ch07.convolutionPower G n)
  exact Kyprianou.Ch07.sumConvolutionTailIntegral
    (Kyprianou.Ch07.convolutionPower G n) G x
