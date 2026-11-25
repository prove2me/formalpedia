-- Prove2me | solution 1 for Kyprianou.Ch04.idleOccupationNatHorizonSupV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:16:48.92074+00:00
-- url     : https://prove2.me/submissions/2685152e-f3e7-445a-8cbe-6d0c14bd638e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (A : Set Real) (hA : MeasurableSet A) :
    (∫⁻ t in Ici (0 : Real), A.indicator (fun _ => (1 : ENNReal)) t ∂volume) =
      ⨆ n : Nat, ∫⁻ t in Icc (0 : Real) (n : Real),
        A.indicator (fun _ => (1 : ENNReal)) t ∂volume := by
  classical
  let B : Nat → Set Real := fun n => A ∩ Icc 0 (n : Real)
  have hB : Monotone B := fun m n hmn t ht => ⟨ht.1, ht.2.1,
    ht.2.2.trans (Nat.cast_le.mpr hmn)⟩
  have hU : (⋃ n, B n) = A ∩ Ici 0 := by
    ext t
    simp only [B, mem_iUnion, mem_inter_iff, mem_Icc, mem_Ici]
    constructor
    · rintro ⟨n, ha, h0, _⟩; exact ⟨ha, h0⟩
    · rintro ⟨ha, h0⟩
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, ha, h0, hn⟩
  have h (s : Set Real) :
      (∫⁻ t in s, A.indicator (fun _ => (1 : ENNReal)) t ∂volume) =
        volume (A ∩ s) := by
    rw [← Measure.restrict_apply hA]
    exact lintegral_indicator_one hA
  simp_rw [h]
  rw [← hU, hB.measure_iUnion]
