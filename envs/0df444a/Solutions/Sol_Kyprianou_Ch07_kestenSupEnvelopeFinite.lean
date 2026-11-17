-- Prove2me | solution 1 for Kyprianou.Ch07.kestenSupEnvelopeFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:36:53.67985+00:00
-- url     : https://prove2.me/submissions/6c27dc00-75b2-45cf-b261-9caa98b766cc

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenSupRatioBounded
import Theorems.Thm_Kyprianou_Ch07_kestenEachOrderHasFiniteTailBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConv : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧
        (∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤
              Kyprianou.Ch07.kestenSupEnvelope G n) ∧
        Kyprianou.Ch07.kestenSupEnvelope G n ≤ C := by
  intro n hn
  obtain ⟨C, hC, hBound⟩ :=
    Kyprianou.Ch07.kestenEachOrderHasFiniteTailBound
      G hPositiveTail hConv n hn
  refine ⟨C, hC, ?_, ?_⟩
  · intro x hx
    have h := (Kyprianou.Ch07.kestenSupRatioBounded G n C
      hBound x hx).1
    simpa only [Kyprianou.Ch07.kestenSupEnvelope] using h
  · have h := (Kyprianou.Ch07.kestenSupRatioBounded G n C
      hBound 1 (by norm_num)).2
    simpa only [Kyprianou.Ch07.kestenSupEnvelope] using h
