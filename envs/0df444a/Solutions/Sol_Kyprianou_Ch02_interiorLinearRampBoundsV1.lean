-- Prove2me | solution 1 for Kyprianou.Ch02.interiorLinearRampBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:12:57.951339+00:00
-- url     : https://prove2.me/submissions/f91a4ed1-96ff-446a-b48f-8e9783ab21f9

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (r : ℝ) (hr : 0 < r) (n : ℕ) (x : ℝ) :
    let g : ℝ := min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))
    0 ≤ g ∧ g ≤ (Ioo (0 : ℝ) r).indicator id x ∧ g ≤ r ∧
      (|x| < 1 / ((n : ℝ) + 1) → g = 0) := by
  let g : ℝ := min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))
  change 0 ≤ g ∧ g ≤ (Ioo (0 : ℝ) r).indicator id x ∧ g ≤ r ∧
    (|x| < 1 / ((n : ℝ) + 1) → g = 0)
  have h0 : 0 ≤ g := le_min (le_max_left _ _) (le_max_left _ _)
  have hle : g ≤ (Ioo (0 : ℝ) r).indicator id x := by
    by_cases hx : x ∈ Ioo (0 : ℝ) r
    · rw [indicator_of_mem hx]
      exact (min_le_left _ _).trans (max_le hx.1.le (sub_le_self _ (by positivity)))
    · rw [indicator_of_notMem hx]
      by_cases h : 0 < x
      · have hxr : r ≤ x := le_of_not_gt (fun hxr => hx ⟨h, hxr⟩)
        exact (min_le_right _ _).trans (max_le le_rfl
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hxr)))
      · exact (min_le_left _ _).trans (max_le le_rfl
          (sub_nonpos.mpr ((le_of_not_gt h).trans (by positivity))))
  refine ⟨h0, hle, hle.trans ?_, ?_⟩
  · by_cases hx : x ∈ Ioo (0 : ℝ) r
    · simpa [hx] using hx.2.le
    · simp [hx, hr.le]
  · intro hx
    exact le_antisymm ((min_le_left _ _).trans
      (max_le le_rfl (sub_nonpos.mpr (abs_lt.mp hx).2.le))) h0
