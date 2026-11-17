-- Prove2me | solution 1 for Kyprianou.Ch06.threeMarkedCountVennPartitionAe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:44:05.092248+00:00
-- url     : https://prove2.me/submissions/2619a8e9-34f7-4dd2-9633-fa18f6daee5c

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
    (B C D : Set E) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t B =
        N omega t ((B \ C) \ D) +
        N omega t ((B ∩ C) \ D) +
        N omega t ((B ∩ D) \ C) +
        N omega t (B ∩ C ∩ D) ∧
      N omega t C =
        N omega t ((C \ B) \ D) +
        N omega t ((B ∩ C) \ D) +
        N omega t ((C ∩ D) \ B) +
        N omega t (B ∩ C ∩ D) ∧
      N omega t D =
        N omega t ((D \ B) \ C) +
        N omega t ((B ∩ D) \ C) +
        N omega t ((C ∩ D) \ B) +
        N omega t (B ∩ C ∩ D) := by
  have hBC := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP B C
  have hCB := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP C B
  have hBD := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP (B \ C) D
  have hCD := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP (C \ B) D
  have hBCD := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP (B ∩ C) D
  have hDB := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP D B
  have hDC := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP (D \ B) C
  have hDBC := Kyprianou.Ch06.overlappingMarkedCountSpatialPartitionAe P n N hPPP (D ∩ B) C
  have hE : (B \ C) ∩ D = (B ∩ D) \ C := by
    ext x; simp [Set.mem_diff,Set.mem_inter_iff]; tauto
  have hF : (C \ B) ∩ D = (C ∩ D) \ B := by
    ext x; simp [Set.mem_diff,Set.mem_inter_iff]; tauto
  have hCBSet : C ∩ B = B ∩ C := Set.inter_comm C B
  have hDBSet : D ∩ B = B ∩ D := Set.inter_comm D B
  have hF2 : (D \ B) ∩ C = (C ∩ D) \ B := by
    ext x; simp [Set.mem_diff,Set.mem_inter_iff]; tauto
  have hE2 : (D ∩ B) \ C = (B ∩ D) \ C := by
    rw [Set.inter_comm]
  have hG : (D ∩ B) ∩ C = B ∩ C ∩ D := by
    ext x; simp [Set.mem_inter_iff]; tauto
  filter_upwards [hBC,hCB,hBD,hCD,hBCD,hDB,hDC,hDBC]
    with omega hbc hcb hbd hcd hbcd hdb hdc hdbc
  intro t
  have hB0 := (hbc t).1
  have hB1 := (hbd t).1
  have hB2 := (hbcd t).1
  have hC0 := (hcb t).1
  have hC1 := (hcd t).1
  have hC2 := (hbcd t).1
  have hD0 := (hdb t).1
  have hD1 := (hdc t).1
  have hD2 := (hdbc t).1
  rw [hE] at hB1
  rw [hF] at hC1
  rw [hCBSet] at hC0
  rw [hF2] at hD1
  rw [hE2,hG] at hD2
  rw [hDBSet] at hD0
  rw [hDBSet] at hD2
  constructor
  · omega
  constructor
  · omega
  · omega
