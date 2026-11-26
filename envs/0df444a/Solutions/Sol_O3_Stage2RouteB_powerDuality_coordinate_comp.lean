-- Prove2me | solution 1 for O3.Stage2RouteB.powerDuality_coordinate_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:39.220614+00:00
-- url     : https://prove2.me/submissions/aded44ce-8c28-45e5-819d-fe881a151aac

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_abs_powerDuality_coordinate
import Theorems.Thm_O3_Stage2RouteB_inner_comp_exponent

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p a : ℝ} (hp : 1 < p) :
    |(|a| ^ (p - 2) * a)| ^ (conjugateExponent p - 2) *
        (|a| ^ (p - 2) * a) = a := by
  by_cases ha : a = 0
  · subst a
    ring
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [abs_powerDuality_coordinate hp]
    rw [← Real.rpow_mul habs.le]
    rw [show |a| ^ ((p - 1) * (conjugateExponent p - 2)) *
        (|a| ^ (p - 2) * a) =
        |a| ^ ((p - 1) * (conjugateExponent p - 2)) *
          |a| ^ (p - 2) * a by ring]
    rw [← Real.rpow_add habs]
    rw [inner_comp_exponent hp, Real.rpow_zero]
    ring
end O3.Stage2RouteB
