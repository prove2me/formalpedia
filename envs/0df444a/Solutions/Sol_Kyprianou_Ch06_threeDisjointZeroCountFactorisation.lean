-- Prove2me | solution 1 for Kyprianou.Ch06.threeDisjointZeroCountFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:45:32.75759+00:00
-- url     : https://prove2.me/submissions/273722cb-e8cc-4b8f-ab68-b8ff07ac04f6

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_threeDisjointMarkedPoissonCountIndependence
import Theorems.Thm_Kyprianou_Ch06_disjointMarkedPoissonCountIndependence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (t u v : NNReal) (k l : Nat) :
    P {omega | N omega t A = 0 ∧ N omega u B = k ∧
      N omega v C = l} =
    P {omega | N omega t A = 0} *
      P {omega | N omega u B = k ∧ N omega v C = l} := by
  have hTriple :=
    Kyprianou.Ch06.threeDisjointMarkedPoissonCountIndependence
      P n N hPPP A B C hA hB hC hAB hAC hBC
      hFA hFB hFC t u v 0 k l
  have hTwo :=
    Kyprianou.Ch06.disjointMarkedPoissonCountIndependence
      P n N hPPP B C hB hC hBC hFB hFC u v k l
  calc
    P {omega | N omega t A = 0 ∧ N omega u B = k ∧
      N omega v C = l} =
        P {omega | N omega t A = 0} *
        P {omega | N omega u B = k} *
        P {omega | N omega v C = l} := hTriple
    _ = P {omega | N omega t A = 0} *
        (P {omega | N omega u B = k} *
         P {omega | N omega v C = l}) := by rw [mul_assoc]
    _ = P {omega | N omega t A = 0} *
        P {omega | N omega u B = k ∧ N omega v C = l} := by
      rw [hTwo]
