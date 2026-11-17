-- Prove2me | solution 1 for Kyprianou.Ch06.threeOrderedRepeatedMarkedCountsEqualIncrementsAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:22:15.080325+00:00
-- url     : https://prove2.me/submissions/54ffe8af-ad6c-4cb1-9d41-4790f1145b8b

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
    (k l q : Nat) (hkl : k ≤ l) (hlq : l ≤ q) :
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t B = l ∧
        N omega u B = q) ↔
      (N omega s B-N omega 0 B = k ∧
        N omega t B-N omega s B = l-k ∧
        N omega u B-N omega t B = q-l) := by
  filter_upwards [hPPP.2.1] with omega hw
  have hInitial : N omega 0 B = 0 := hw.1 B
  have hMono1 : N omega s B ≤ N omega t B := hw.2.2 B hst
  have hMono2 : N omega t B ≤ N omega u B := hw.2.2 B htu
  omega
