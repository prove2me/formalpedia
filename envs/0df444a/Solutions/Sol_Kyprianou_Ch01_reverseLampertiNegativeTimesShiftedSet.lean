-- Prove2me | solution 1 for Kyprianou.Ch01.reverseLampertiNegativeTimesShiftedSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:00:07.870719+00:00
-- url     : https://prove2.me/submissions/10897e49-d519-4e01-ad25-95d0ed5b1d0d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_nonnegativeSInfTranslatedImage
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (y : ℕ) (hy : 0 < y) (t : ℝ≥0)
    (A : ℝ) (hA : 0 ≤ A)
    (hFirst : A ≤ (y : ℝ) * (t : ℝ))
    (hPrefix : ∀ s : ℝ≥0, (s : ℝ) < A → X s ω = (y : ℤ))
    (hShift : ∀ u : ℝ≥0, A ≤ (u : ℝ) →
      X u ω = Y (Real.toNNReal ((u : ℝ) - A)) ω)
    (hTailNonnegative : (0 : ℤ) ≤ Y 0 ω) :
    {u : ℝ≥0 | 0 < u ∧ X u ω < 0} =
      (fun v : ℝ≥0 => Real.toNNReal A + v) ''
        {v : ℝ≥0 | 0 < v ∧ Y v ω < 0} := by
  classical
  let a : ℝ≥0 := Real.toNNReal A
  have ha : (a : ℝ) = A := Real.coe_toNNReal A hA
  let P : Set ℝ≥0 := {u | 0 < u ∧ X u ω < 0}
  let S : Set ℝ≥0 := {v | 0 < v ∧ Y v ω < 0}
  have hMem (u : ℝ≥0) :
      u ∈ P ↔ ∃ v ∈ S, u = a + v := by
    constructor
    · intro hu
      obtain ⟨hu0, hneg⟩ := hu
      have hAu : a ≤ u := by
        by_contra hn
        have hlt : u < a := lt_of_not_ge hn
        have hltR : (u : ℝ) < A := by
          rw [← ha]
          exact_mod_cast hlt
        have hpos : (0 : ℤ) ≤ X u ω := by
          rw [hPrefix u hltR]
          exact Int.natCast_nonneg _
        exact (not_lt.mpr hpos) hneg
      let v : ℝ≥0 := u - a
      have hvreal : (v : ℝ) = (u : ℝ) - A := by
        change ((u - a : ℝ≥0) : ℝ) = (u : ℝ) - A
        rw [NNReal.coe_sub hAu, ha]
      have hvclock : Real.toNNReal ((u : ℝ) - A) = v := by
        rw [← hvreal]
        simp [v]
      have hvneg : Y v ω < 0 := by
        have hShiftU := hShift u (by rw [← ha]; exact_mod_cast hAu)
        rw [hvclock] at hShiftU
        rwa [hShiftU] at hneg
      have hvpos : 0 < v := by
        by_contra hn
        have hvzero : v = 0 := le_antisymm (le_of_not_gt hn) (show (0 : ℝ≥0) ≤ v from zero_le)
        rw [hvzero] at hvneg
        exact (not_lt.mpr hTailNonnegative) hvneg
      exact ⟨v, ⟨hvpos, hvneg⟩, (add_tsub_cancel_of_le hAu).symm⟩
    · rintro ⟨v, ⟨hvpos, hvneg⟩, rfl⟩
      have hBound : A ≤ (((a + v : ℝ≥0) : ℝ)) := by
        rw [NNReal.coe_add, ha]
        exact le_add_of_nonneg_right v.property
      have hReal : Real.toNNReal ((((a + v : ℝ≥0) : ℝ)) - A) = v := by
        rw [NNReal.coe_add, ha]
        simp
      have hShiftU := hShift (a + v) hBound
      have hPos : (0 : ℝ≥0) < a + v :=
        lt_of_le_of_lt (show (0 : ℝ≥0) ≤ a from zero_le) (lt_add_of_pos_right a hvpos)
      refine ⟨hPos, ?_⟩
      rw [hShiftU, hReal]
      exact hvneg
  ext u
  constructor
  · intro hu
    rcases (hMem u).mp hu with ⟨v, hv, heq⟩
    exact ⟨v, hv, heq.symm⟩
  · rintro ⟨v, hv, heq⟩
    exact (hMem u).mpr ⟨v, hv, heq.symm⟩
