-- Prove2me | solution 1 for Kyprianou.Ch06.disjointTwoZeroCountsIndependentOfOutsideCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:12:02.947167+00:00
-- url     : https://prove2.me/submissions/03572703-f342-4c52-b554-875e7392a214

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
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
    (B D C : Set E)
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hC : MeasurableSet C)
    (hBD : Disjoint B D) (hBC : Disjoint B C)
    (hDC : Disjoint D C)
    (hFB : n B < ⊤) (hFD : n D < ⊤) (hFC : n C < ⊤)
    (s t u : NNReal) (k : Nat) :
    P {omega |
      N omega s B = 0 ∧ N omega t D = 0 ∧ N omega u C = k} =
    P {omega | N omega s B = 0 ∧ N omega t D = 0} *
      P {omega | N omega u C = k} := by
  have hTriple :=
    Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
      P n N hPPP B D C hB hD hC hBD hBC hDC
      hFB hFD hFC s t u 0 0 k
  have hPair :=
    Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
      P n N hPPP B D hB hD hBD hFB hFD s t 0 0
  calc
    _ = P {omega | N omega s B = 0} *
          P {omega | N omega t D = 0} *
          P {omega | N omega u C = k} := hTriple
    _ = P {omega | N omega s B = 0 ∧ N omega t D = 0} *
          P {omega | N omega u C = k} := by rw [hPair]
