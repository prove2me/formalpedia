-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.finite_nat_cube_union_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:34:50.374331+00:00
-- url     : https://prove2.me/submissions/abb68922-268e-4989-bacc-e77a33a778c2

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_iUnion_finset_eq_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nat_cube_family_facts

open scoped BigOperators

theorem solution
    {m : ℕ} (S : Finset (Fin m → ℕ)) :
    MeasureTheory.volume {x : Fin m → ℝ | ∃ a ∈ S, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
      (S.card : ENNReal) := by
  obtain ⟨hmeas, hdisj, hvol⟩ :=
    OAI.PiExponent.DeterminantContradiction.nat_cube_family_facts S
  calc
    MeasureTheory.volume
        {x : Fin m → ℝ | ∃ a ∈ S, ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} =
        MeasureTheory.volume (⋃ a ∈ S,
          {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}) := by
            congr 1
            ext x
            simp
    _ = ∑ a ∈ S,
          MeasureTheory.volume
            {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1} :=
      OAI.PiExponent.DeterminantContradiction.volume_iUnion_finset_eq_sum
        S (fun a => {x : Fin m → ℝ | ∀ i, (a i : ℝ) ≤ x i ∧ x i < (a i : ℝ) + 1}) hmeas hdisj
    _ = ∑ _a ∈ S, (1 : ENNReal) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hvol a ha
    _ = (S.card : ENNReal) := by
      simp
