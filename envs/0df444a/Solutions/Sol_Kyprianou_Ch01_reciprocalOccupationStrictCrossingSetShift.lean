-- Prove2me | solution 1 for Kyprianou.Ch01.reciprocalOccupationStrictCrossingSetShift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:11:15.819379+00:00
-- url     : https://prove2.me/submissions/abc4bb82-e44f-4c34-b6a6-047a8e3137c2

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationPhysicalRestartShift
import Theorems.Thm_Kyprianou_Ch01_reciprocalOccupationMonotone
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
    {u : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X u ω} =
      (fun v : ℝ≥0 => Real.toNNReal A + v) ''
        {v : ℝ≥0 |
          ((Real.toNNReal ((t : ℝ) - A / (y : ℝ)) : ℝ≥0) : ℝ≥0∞) <
            reciprocalOccupation Y v ω} := by
  classical
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hClock : A / (y : ℝ) ≤ (t : ℝ) :=
    (div_le_iff₀ hyR).mpr (by nlinarith [hFirst])
  have hClock0 : 0 ≤ A / (y : ℝ) := div_nonneg hA (le_of_lt hyR)
  have hResidual0 : 0 ≤ (t : ℝ) - A / (y : ℝ) := sub_nonneg.mpr hClock
  let a : ℝ≥0 := Real.toNNReal A
  let q : ℝ≥0 := Real.toNNReal (A / (y : ℝ))
  let r : ℝ≥0 := Real.toNNReal ((t : ℝ) - A / (y : ℝ))
  have ha : (a : ℝ) = A := Real.coe_toNNReal A hA
  have hSumNN : q + r = t := by
    apply NNReal.eq
    change (q : ℝ) + (r : ℝ) = (t : ℝ)
    rw [Real.coe_toNNReal (A / (y : ℝ)) hClock0,
      Real.coe_toNNReal ((t : ℝ) - A / (y : ℝ)) hResidual0]
    ring
  have hSum : (t : ℝ≥0∞) = (q : ℝ≥0∞) + (r : ℝ≥0∞) := by
    calc
      (t : ℝ≥0∞) = ((q + r : ℝ≥0) : ℝ≥0∞) :=
        congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hSumNN.symm
      _ = (q : ℝ≥0∞) + (r : ℝ≥0∞) := by norm_cast
  have hAt (v : ℝ≥0) :
      reciprocalOccupation X (a + v) ω =
      (q : ℝ≥0∞) + reciprocalOccupation Y v ω := by
    have hBound : A ≤ (((a + v : ℝ≥0) : ℝ)) := by
      rw [NNReal.coe_add, ha]
      exact le_add_of_nonneg_right v.property
    have hReal : Real.toNNReal ((((a + v : ℝ≥0) : ℝ)) - A) = v := by
      rw [NNReal.coe_add, ha]
      simp
    have hShiftU := reciprocalOccupationPhysicalRestartShift
      X Y ω y hy t A hA hFirst hPrefix hShift hTailNonnegative (a + v) hBound
    rw [hReal] at hShiftU
    simpa [q, ENNReal.ofReal_eq_coe_nnreal hClock0,
      Real.toNNReal_of_nonneg hClock0] using hShiftU
  have hZero : reciprocalOccupation Y 0 ω = 0 := by
    simp [reciprocalOccupation]
  have hAtA : reciprocalOccupation X a ω = (q : ℝ≥0∞) := by
    simpa [hZero] using hAt 0
  have hQLe : (q : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
    rw [hSum]
    exact le_add_of_nonneg_right zero_le
  have hIff (v : ℝ≥0) :
      ((t : ℝ≥0∞) < reciprocalOccupation X (a + v) ω) ↔
      ((r : ℝ≥0∞) < reciprocalOccupation Y v ω) := by
    rw [hSum, hAt]
    exact ENNReal.add_lt_add_iff_left (by simp)
  ext u
  constructor
  · intro hu
    have hAu : a ≤ u := by
      by_contra hn
      have hLt : u < a := lt_of_not_ge hn
      have hLe : reciprocalOccupation X u ω ≤ (q : ℝ≥0∞) :=
        (reciprocalOccupationMonotone X ω (le_of_lt hLt)).trans_eq hAtA
      exact (not_lt.mpr (hLe.trans hQLe)) hu
    let v : ℝ≥0 := u - a
    have huEq : u = a + v := (add_tsub_cancel_of_le hAu).symm
    have hCross : (r : ℝ≥0∞) < reciprocalOccupation Y v ω :=
      (hIff v).mp (by rwa [← huEq])
    exact ⟨v, hCross, huEq.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact (hIff v).mpr hv
