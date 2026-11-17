-- Prove2me | solution 1 for Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:55.265056+00:00
-- url     : https://prove2.me/submissions/64849fa9-42e8-425e-a4a6-b03632305ec5

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N) :
    IsProbabilityMeasure P := by
  have hEmpty := hPPP.2.2 0
    (fun _ : Fin 0 => (0 : NNReal))
    (fun _ : Fin 0 => (0 : NNReal))
    (fun _ : Fin 0 => (∅ : Set E))
    (fun _ : Fin 0 => 0)
    (by intro i; exact i.elim0)
    (by intro i j hij; exact i.elim0)
  have hMass : P Set.univ = 1 := by simpa using hEmpty
  exact ⟨hMass⟩
