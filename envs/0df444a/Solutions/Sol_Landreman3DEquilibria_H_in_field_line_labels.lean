-- Prove2me | solution 1 for Landreman3DEquilibria.H_in_field_line_labels
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T19:25:07.785541+00:00
-- url     : https://prove2.me/submissions/09cbe658-4d6b-41c4-a2fd-5fcfe442d0b1

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family
import Theorems.Thm_Landreman3DEquilibria_H_field_line_constant
import Theorems.Thm_Landreman3DEquilibria_H_at_toroidal_zero

open Landreman3DEquilibria

theorem solution (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v z) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) := by
  rw [H_field_line_constant e u v z he he1 huv]
  exact H_at_toroidal_zero e u v he he1 huv
