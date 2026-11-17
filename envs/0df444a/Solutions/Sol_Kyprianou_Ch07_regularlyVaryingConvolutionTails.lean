-- Prove2me | solution 1 for Kyprianou.Ch07.regularlyVaryingConvolutionTails
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:24:52.026579+00:00
-- url     : https://prove2.me/submissions/4dab6ce2-bd15-430e-9e59-fe7f250bb8be
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_regularVariationConvolutionTwofold_v2
import Theorems.Thm_Kyprianou_Ch07_regularVariationConvolutionStep_v2
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    (PiH : Measure Real) (alpha : Real)
    (hAlpha : 0 < alpha)
    (hPositiveJumpSupport : PiH (Set.Iic (0 : Real)) = 0)
    (hLargeFinite : PiH (Set.Ioi (1 : Real)) < ⊤)
    (hLargePositive : 0 < PiH (Set.Ioi (1 : Real)))
    (hRegular : Kyprianou.Ch05.RegularlyVaryingAtInfinity
      (fun x : Real => (PiH (Set.Ioi x)).toReal) (-alpha)) :
    let nu : Measure Real := largeJumpNormalisedLaw PiH
    ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower nu n) (Set.Ioi x)).toReal /
          ((n : Real) * (nu (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real)) := by
  dsimp only
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      exact Kyprianou.Ch07.regularVariationConvolutionTwofold_v2
        PiH alpha hAlpha hPositiveJumpSupport hLargeFinite
        hLargePositive hRegular
  | succ n hn ih =>
      exact Kyprianou.Ch07.regularVariationConvolutionStep_v2
        PiH alpha hAlpha hPositiveJumpSupport hLargeFinite
        hLargePositive hRegular n hn ih
