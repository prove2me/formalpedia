-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_successor_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:48:21.857119+00:00
-- url     : https://prove2.me/submissions/de41476a-fd9c-4d6c-8a25-7a6f4b55a396

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_coordinate_slicing
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_nonnegative_dilation

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) /
      (n + 1 : ℝ) := by
  have hint : (∫ t in (0 : ℝ)..1, (1 - t) ^ n) = 1 / (n + 1 : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t) ^ n) = ∫ t in (0 : ℝ)..1, t ^ n := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := (1 : ℝ))
            (fun t : ℝ => t ^ n) (1 : ℝ))
      _ = 1 / (n + 1 : ℝ) := by
        simp [integral_pow]
  have hslices :
      (∫ t in (0 : ℝ)..1, ENNReal.toReal (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1 - t})) =
      (∫ t in (0 : ℝ)..1, (1 - t) ^ n) *
        ENNReal.toReal (MeasureTheory.volume
          {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (1 - t) ^ n *
          ENNReal.toReal (MeasureTheory.volume
            {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact OAI.PiExponent.DeterminantContradiction.simplexVolume_nonnegative_dilation
          n (1 - t) (sub_nonneg.mpr ht.2)
      _ = _ := intervalIntegral.integral_mul_const _ _
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_coordinate_slicing n,
    hslices, hint]
  simp only [div_eq_mul_inv, one_mul]
  exact mul_comm _ _