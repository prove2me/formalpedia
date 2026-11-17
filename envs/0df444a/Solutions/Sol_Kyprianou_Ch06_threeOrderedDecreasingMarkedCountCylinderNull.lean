-- Prove2me | solution 1 for Kyprianou.Ch06.threeOrderedDecreasingMarkedCountCylinderNull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:23:51.5032+00:00
-- url     : https://prove2.me/submissions/e58fb263-a78a-4260-8885-a223dc911dca

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
    (B : Set E) (s t u : NNReal) (hst : s ≤ t) (htu : t ≤ u)
    (k l q : Nat) (hBad : l < k ∨ q < l) :
    P {omega | N omega s B = k ∧
      N omega t B = l ∧ N omega u B = q} = 0 := by
  have hImpossible : ∀ᵐ omega ∂P,
      ¬ (N omega s B = k ∧
        N omega t B = l ∧ N omega u B = q) := by
    filter_upwards [hPPP.2.1] with omega hw h
    have hMono1 : N omega s B ≤ N omega t B := hw.2.2 B hst
    have hMono2 : N omega t B ≤ N omega u B := hw.2.2 B htu
    omega
  have hMeasure :
      P ({omega | ¬ (N omega s B = k ∧
          N omega t B = l ∧ N omega u B = q)} : Set Omega)ᶜ = 0 :=
    (MeasureTheory.mem_ae_iff).mp hImpossible
  simpa only [Set.compl_setOf,not_not] using hMeasure
