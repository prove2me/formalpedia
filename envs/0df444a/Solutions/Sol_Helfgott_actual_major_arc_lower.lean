-- Prove2me | solution 1 for Helfgott.actual_major_arc_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T05:42:45.491711+00:00
-- url     : https://prove2.me/submissions/9ee47b61-9ec1-440c-bc6f-6367bc478a44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_actual_major_arc_lower_of_low_zero_locations
import Theorems.Thm_Helfgott_primitive_low_zero_locations_of_finite_grh_profile
import Theorems.Thm_Helfgott_actual_primitive_finite_grh_profile
import Mathlib.Tactic
open MeasureTheory Helfgott
theorem solution (N : ℕ) (hN : 10^27 ≤ N) (hodd : Odd N) :
    (1058259/1000000 : ℝ)*((goldbachScale N)^2/49) ≤
      (∫ α in majorArcs 8 150000 (goldbachScale N),
        ternaryIntegrand (goldbachScale N) N α ∂AddCircle.haarAddCircle).re := by
  exact actual_major_arc_lower_of_low_zero_locations
    (primitive_low_zero_locations_of_finite_grh_profile actual_primitive_finite_grh_profile)
    N hN hodd
#print axioms solution
