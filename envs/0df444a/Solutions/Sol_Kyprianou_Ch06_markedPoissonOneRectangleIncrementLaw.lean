-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonOneRectangleIncrementLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T07:38:16.563453+00:00
-- url     : https://prove2.me/submissions/438b44a5-3e2d-4fb9-9b4d-c5c58c88bbb1

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (s t : NNReal) (hSt : s ≤ t)
    (A : Set E) (hA : MeasurableSet A) (hFinite : n A < ⊤)
    (k : Nat) :
  P {omega | N omega t A - N omega s A = k} =
    ProbabilityTheory.poissonMeasure ((t - s) * (n A).toNNReal) {k} := by
  have h := hPPP.2.2 1 (fun _ => s) (fun _ => t)
    (fun _ => A) (fun _ => k)
    (by intro i; exact ⟨hSt, hA, hFinite⟩)
    (by
      intro i j hij
      exact False.elim (hij (Subsingleton.elim i j)))
  simpa using h
