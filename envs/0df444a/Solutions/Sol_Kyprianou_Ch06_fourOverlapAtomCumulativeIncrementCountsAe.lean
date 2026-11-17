-- Prove2me | solution 1 for Kyprianou.Ch06.fourOverlapAtomCumulativeIncrementCountsAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:38:18.483467+00:00
-- url     : https://prove2.me/submissions/54e01730-f6ab-4eb8-80a8-b597fbd14f1f

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
    (B C : Set E) (s t : NNReal) (x y z w : Nat) :
    ∀ᵐ omega ∂P,
      (N omega s (B \ C) = x ∧
       N omega s (B ∩ C) = y ∧
       N omega s (C \ B) = z ∧
       N omega t C-N omega s C = w) ↔
      (N omega s (B \ C)-N omega 0 (B \ C) = x ∧
       N omega s (B ∩ C)-N omega 0 (B ∩ C) = y ∧
       N omega s (C \ B)-N omega 0 (C \ B) = z ∧
       N omega t C-N omega s C = w) := by
  filter_upwards [hPPP.2.1] with omega hw
  simp [hw.1 (B \ C), hw.1 (B ∩ C), hw.1 (C \ B)]
