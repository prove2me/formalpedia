-- Prove2me | solution 1 for Kyprianou.Ch06.differentTimesOverlapCountCylinderAsFiniteAtomUnionAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:31:36.408531+00:00
-- url     : https://prove2.me/submissions/d725bfe4-d51f-453b-9ef2-878e5de2da8f

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
    (B C : Set E) (s t : NNReal) (hst : s ≤ t)
    (k l : Nat) :
    let F : (Fin (k+1) × Fin (l+1)) → Set Omega :=
      fun i => {omega |
        (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
        N omega s (B \ C) = k-(i.1 : Nat) ∧
        N omega s (B ∩ C) = (i.1 : Nat) ∧
        N omega s (C \ B) = (i.2 : Nat) ∧
        N omega t C - N omega s C =
          l-(i.1 : Nat)-(i.2 : Nat)}
    ∀ᵐ omega ∂P,
      (N omega s B = k ∧ N omega t C = l) ↔
      omega ∈ ⋃ i, F i := by
  dsimp only
  have hSpace :=
    Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe
      P n N hPPP B C
  filter_upwards [hPPP.2.1, hSpace] with omega hw hs
  have hB := (hs s).1
  have hC := (hs s).2
  have hTime : N omega s C ≤ N omega t C := hw.2.2 C hst
  constructor
  · rintro ⟨hk,hl⟩
    have hq : N omega s (B ∩ C) < k+1 := by omega
    have hz : N omega s (C \ B) < l+1 := by omega
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨N omega s (B ∩ C),hq⟩,
      ⟨N omega s (C \ B),hz⟩), ?_⟩
    change N omega s (B ∩ C) + N omega s (C \ B) ≤ l ∧
      N omega s (B \ C) = k - N omega s (B ∩ C) ∧
      N omega s (B ∩ C) = N omega s (B ∩ C) ∧
      N omega s (C \ B) = N omega s (C \ B) ∧
      N omega t C - N omega s C =
        l - N omega s (B ∩ C) - N omega s (C \ B)
    omega
  · intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    change (i.1 : Nat) + (i.2 : Nat) ≤ l ∧
      N omega s (B \ C) = k-(i.1 : Nat) ∧
      N omega s (B ∩ C) = (i.1 : Nat) ∧
      N omega s (C \ B) = (i.2 : Nat) ∧
      N omega t C - N omega s C =
        l-(i.1 : Nat)-(i.2 : Nat) at hi
    have hbound := i.1.isLt
    omega
