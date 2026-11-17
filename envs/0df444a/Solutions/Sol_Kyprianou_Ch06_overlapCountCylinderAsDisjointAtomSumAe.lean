-- Prove2me | solution 1 for Kyprianou.Ch06.overlapCountCylinderAsDisjointAtomSumAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:16:51.642723+00:00
-- url     : https://prove2.me/submissions/f5e7793a-8681-4add-9f0a-2bd19966c57a

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
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
    (B C : Set E) (t : NNReal) (k l : Nat) :
    ∀ᵐ omega ∂P,
      (N omega t B = k ∧ N omega t C = l) ↔
      ∃ q : Nat, q ≤ min k l ∧
        N omega t (B \ C) = k - q ∧
        N omega t (C \ B) = l - q ∧
        N omega t (B ∩ C) = q := by
  have hPartition :=
    Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP B C
  filter_upwards [hPartition] with omega h
  obtain ⟨hB, hC⟩ := h t
  constructor
  · rintro ⟨hBk, hCl⟩
    refine ⟨N omega t (B ∩ C), ?_, ?_, ?_, rfl⟩
    · omega
    · omega
    · omega
  · rintro ⟨q, hq, hBq, hCq, hIq⟩
    constructor <;> omega
