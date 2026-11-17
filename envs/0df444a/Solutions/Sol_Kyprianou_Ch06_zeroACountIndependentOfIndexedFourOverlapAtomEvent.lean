-- Prove2me | solution 1 for Kyprianou.Ch06.zeroACountIndependentOfIndexedFourOverlapAtomEvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:47:36.906137+00:00
-- url     : https://prove2.me/submissions/81164e35-6e20-4140-922b-d0d07f80d37d

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
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
    (A B C : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hFA : n A < ⊤) (hFB : n B < ⊤) (hFC : n C < ⊤)
    (r s t : NNReal) (hst : s ≤ t)
    (k l : Nat) (i : Fin (k+1) × Fin (l+1)) :
    P {omega | N omega r A = 0 ∧
      (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)} =
    P {omega | N omega r A = 0} *
    P {omega | (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C = l-(i.1 : Nat)-(i.2 : Nat)} := by
  by_cases hi : (i.1 : Nat) + (i.2 : Nat) ≤ l
  · have h :=
      Kyprianou.Ch06.zeroACountIndependentOfFourOverlapSpacetimeAtomCounts
        P n N hPPP A B C hA hB hC hAB hAC hFA hFB hFC
        r s t hst (k-i.1) i.1 i.2 (l-i.1-i.2)
    simpa only [hi, true_and, and_assoc] using h
  · simp [hi]
