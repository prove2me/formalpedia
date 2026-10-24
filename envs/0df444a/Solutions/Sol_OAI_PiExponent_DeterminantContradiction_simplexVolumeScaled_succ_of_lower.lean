-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_of_lower
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:38:38.066774+00:00
-- url     : https://prove2.me/submissions/3982c295-dc19-4f39-abb8-b0b8f78fa602

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_integral
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r)
    (ih : ∀ s : Real, 0 ≤ s →
      MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ s} =
        ENNReal.ofReal (s ^ n / (Nat.factorial n : Real))) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) := by
  calc
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ∫⁻ t in Set.Icc (0 : Real) r,
        MeasureTheory.volume
          {y : Fin n → Real | (∀ j, 0 ≤ y j) ∧ (∑ j, y j) ≤ r - t}
        ∂MeasureTheory.volume :=
      OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_slice n r hr
    _ = ENNReal.ofReal (r ^ (n + 1) / (Nat.factorial (n + 1) : Real)) :=
      OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_integral n r hr ih