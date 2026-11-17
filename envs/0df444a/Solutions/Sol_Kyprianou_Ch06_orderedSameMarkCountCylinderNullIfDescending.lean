-- Prove2me | solution 1 for Kyprianou.Ch06.orderedSameMarkCountCylinderNullIfDescending
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:18.10325+00:00
-- url     : https://prove2.me/submissions/6af37475-e157-4ade-9265-4ee84a970424

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B : Set E) (s t : NNReal) (hst : s ≤ t)
    (k l : Nat) (hkl : l < k) :
    P {omega | N omega s B = k ∧ N omega t B = l} = 0 := by
  have hImpossible : ∀ᵐ omega ∂P,
      ¬ (N omega s B = k ∧ N omega t B = l) := by
    filter_upwards [hPPP.2.1] with omega hw h
    have hMonotone : N omega s B ≤ N omega t B := hw.2.2 B hst
    omega
  have hMeasure :
      P ({omega | ¬ (N omega s B = k ∧ N omega t B = l)} : Set Omega)ᶜ = 0 :=
    (MeasureTheory.mem_ae_iff).mp hImpossible
  simpa only [Set.compl_setOf, not_not] using hMeasure
