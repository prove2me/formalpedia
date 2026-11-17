-- Prove2me | solution 1 for Kyprianou.Ch06.nullIntensityOverlapCountsEqualDisjointPartsAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:29.484147+00:00
-- url     : https://prove2.me/submissions/e436d1d3-7431-4a1b-962b-f023eb2213e5

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonRectangleLawForcesProbabilityMeasure
import Theorems.Thm_Kyprianou_Ch06_markedPoissonZeroIntensityAllCountsVanish
import Theorems.Thm_Kyprianou_Ch06_overlappingMarkedCountSpatialPartitionAe
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
    (B C : Set E) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNull : n (B ∩ C) = 0) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B = N omega t (B \ C) ∧
      N omega t C = N omega t (C \ B) := by
  letI : IsProbabilityMeasure P :=
    Kyprianou.Ch06.markedPoissonRectangleLawForcesProbabilityMeasure
      P n N hPPP
  have hZero :=
    Kyprianou.Ch06.markedPoissonZeroIntensityAllCountsVanish
      P n N hPPP (B ∩ C) (hB.inter hC) hNull
  have hSplit :=
    Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe
      P n N hPPP B C
  filter_upwards [hZero,hSplit] with omega hz hs
  intro t
  obtain ⟨hFirst,hSecond⟩ := hs t
  have hVanishing := hz t
  constructor <;> omega
