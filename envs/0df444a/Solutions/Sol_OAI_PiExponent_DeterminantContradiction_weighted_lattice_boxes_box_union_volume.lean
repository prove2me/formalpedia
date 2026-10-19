-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_box_union_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:40:02.980333+00:00
-- url     : https://prove2.me/submissions/5c62537f-bd91-4a63-875c-38d6672ee80b

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_lattice_boxes_union_ennreal_sum

open scoped BigOperators

theorem solution
    (m : ℕ) (s : Finset (Fin m → ℕ)) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) :
    (MeasureTheory.volume
      (⋃ a ∈ (s : Set (Fin m → ℕ)),
        {x : Fin m → ℝ | ∀ i,
          w i * (a i : ℝ) ≤ x i ∧ x i < w i * ((a i : ℝ) + 1)})).toReal =
      (s.card : ℝ) * ∏ i : Fin m, w i := by
  classical
  rw [OAI.PiExponent.DeterminantContradiction.weighted_lattice_boxes_union_ennreal_sum
    m s w hw]
  rw [ENNReal.toReal_sum (by
    intro a ha
    apply ENNReal.prod_ne_top
    intro i hi
    exact ENNReal.ofReal_ne_top)]
  have hcoord : ∀ i : Fin m, (ENNReal.ofReal (w i)).toReal = w i := by
    intro i
    exact ENNReal.toReal_ofReal (le_of_lt (hw i))
  simp_rw [ENNReal.toReal_prod, hcoord]
  simp only [Finset.sum_const, nsmul_eq_mul]