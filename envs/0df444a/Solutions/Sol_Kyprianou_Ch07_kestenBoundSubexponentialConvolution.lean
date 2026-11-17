-- Prove2me | solution 1 for Kyprianou.Ch07.kestenBoundSubexponentialConvolution
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:37:33.8392+00:00
-- url     : https://prove2.me/submissions/7219eaef-f436-4e8b-b3b7-9c33f434edfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_kestenFromConvolutionRecurrence
import Theorems.Thm_Kyprianou_Ch07_kestenSubexponentialAffineEnvelope
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConvolutionAsymptotics : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ epsilon : Real, 0 < epsilon →
      ∃ C : Real, 0 < C ∧
        ∀ n : Nat, 1 ≤ n →
          ∀ x : Real, 0 < x →
            ((convolutionPower G n) (Set.Ioi x)).toReal /
              (G (Set.Ioi x)).toReal ≤ C * (1 + epsilon) ^ n := by
  intro epsilon hEpsilon
  obtain ⟨A, B, hA, hB, xi, hBase, hStep, hTail⟩ :=
    Kyprianou.Ch07.kestenSubexponentialAffineEnvelope
      G hPositiveTail hConvolutionAsymptotics epsilon hEpsilon
  exact Kyprianou.Ch07.kestenFromConvolutionRecurrence
    G epsilon hEpsilon A B hA hB xi hBase hStep hTail
