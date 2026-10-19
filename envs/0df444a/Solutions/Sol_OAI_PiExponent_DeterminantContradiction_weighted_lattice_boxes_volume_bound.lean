-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_volume_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:14:24.051395+00:00
-- url     : https://prove2.me/submissions/3e104d7e-c185-4438-affe-6675b48fc16e

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_box_union_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_union_volume_le_expanded_simplex

open scoped BigOperators

theorem solution
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ) (T : ℝ)
    (hw : ∀ i, 0 < w i) (hT : 0 ≤ T)
    (hs : ∀ a ∈ s, ∑ i : Fin m, w i * (a i : ℝ) ≤ T) :
    ((s.card : ℝ) * ∏ i : Fin m, w i) ≤
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i}).toReal := by
  calc
    ((s.card : ℝ) * ∏ i : Fin m, w i) =
        (MeasureTheory.volume
          (⋃ a ∈ (s : Set (Fin m → ℕ)),
            {x : Fin m → ℝ | ∀ i,
              w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)})).toReal := by
        symm
        exact OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_box_union_volume
          m s w hw
    _ ≤
        (MeasureTheory.volume
          {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧
            ∑ i : Fin m, x i ≤ T + ∑ i : Fin m, w i}).toReal :=
      OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_volume_le_expanded_simplex
        m s w T hw hT hs