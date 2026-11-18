-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonRectangleAxiomNormalisesProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T11:19:24.038463+00:00
-- url     : https://prove2.me/submissions/508ad481-6640-4c0a-a213-3e5cbc03adec

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
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    P Set.univ = 1 := by
  have hRect :=
    hPPP.2.2 0 (fun _ => 0) (fun _ => 0)
      (fun _ => (∅ : Set E)) (fun _ => 0)
      (by intro i; exact Fin.elim0 i)
      (by intro i; exact Fin.elim0 i)
  simpa using hRect
