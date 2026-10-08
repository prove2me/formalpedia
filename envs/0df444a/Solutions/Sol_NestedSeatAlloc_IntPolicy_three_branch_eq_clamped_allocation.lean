-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.three_branch_eq_clamped_allocation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:54:10.219359+00:00
-- url     : https://prove2.me/submissions/21ccedee-7bb9-460f-b56f-c8c46fd5d03d

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (g : ℝ → ℝ) (a c y s : ℝ) (hy : 0 ≤ y) :
    (if s < a then g s else if s < a + y then
       (s - a) * c + g a else y * c + g (s - y)) =
    c * min (max (s - a) 0) y +
      g (s - min (max (s - a) 0) y) := by
  by_cases hsa : s < a
  · have hu : min (max (s - a) 0) y = 0 := by
      rw [max_eq_right (by linarith : s - a ≤ (0 : ℝ)), min_eq_left hy]
    simp [hsa, hu]
  · by_cases hmid : s < a + y
    · have hu : min (max (s - a) 0) y = s - a := by
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ s - a),
          min_eq_left (by linarith : s - a ≤ y)]
      simp [hsa, hmid, hu]
      ring
    · have hu : min (max (s - a) 0) y = y := by
        rw [max_eq_left (by linarith : (0 : ℝ) ≤ s - a),
          min_eq_right (by linarith : y ≤ s - a)]
      simp [hsa, hmid, hu]
      ring
