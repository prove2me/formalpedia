-- Prove2me | solution 1 for Kyprianou.Ch06.orderedSameMarkCountsEquivalentToIncrementCountsAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:11.459448+00:00
-- url     : https://prove2.me/submissions/d3dfc6b2-1566-458b-b49c-507f4beb1d97

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
    (k l : Nat) (hkl : k ≤ l) :
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t B = l) ↔
      (N omega s B - N omega 0 B = k ∧
        N omega t B - N omega s B = l-k) := by
  filter_upwards [hPPP.2.1] with omega hw
  have hInitial := hw.1 B
  have hMonotone : N omega s B ≤ N omega t B := hw.2.2 B hst
  omega
