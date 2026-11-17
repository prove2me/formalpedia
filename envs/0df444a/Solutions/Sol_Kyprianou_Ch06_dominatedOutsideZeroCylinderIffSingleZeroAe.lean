-- Prove2me | solution 1 for Kyprianou.Ch06.dominatedOutsideZeroCylinderIffSingleZeroAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:05:47.752553+00:00
-- url     : https://prove2.me/submissions/47912327-dab9-4a6b-a309-ea5f69fcaa02

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonCountMonotoneInMarksAllTimesAe
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
    (m : Nat) (times : Fin m → NNReal)
    (B : Fin m → Set E) (u : Fin m)
    (hDom : ∀ i : Fin m, B i ⊆ B u ∧ times i ≤ times u) :
    ∀ᵐ omega ∂P,
      (∀ i : Fin m, N omega (times i) (B i) = 0) ↔
        N omega (times u) (B u) = 0 := by
  have hSpace :=
    Kyprianou.Ch06.markedPoissonCountMonotoneInMarksAllTimesAe
      P n N hPPP
  filter_upwards [hPPP.2.1, hSpace] with omega hw hs
  constructor
  · intro hall
    exact hall u
  · intro hz i
    have hTime : N omega (times i) (B i) ≤
        N omega (times u) (B i) :=
      hw.2.2 (B i) (hDom i).2
    have hMark : N omega (times u) (B i) ≤
        N omega (times u) (B u) :=
      hs (B i) (B u) (hDom i).1 (times u)
    omega
