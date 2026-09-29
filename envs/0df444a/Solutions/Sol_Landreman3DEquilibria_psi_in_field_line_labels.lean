-- Prove2me | solution 1 for Landreman3DEquilibria.psi_in_field_line_labels
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T19:21:42.795263+00:00
-- url     : https://prove2.me/submissions/519bcfd3-2e3f-48de-ae52-0daf90405914

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family
import Theorems.Thm_Landreman3DEquilibria_H_in_field_line_labels

open Landreman3DEquilibria

theorem solution (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    psiFun e (posMap e u v z) = (u + e / 2) ^ 2 + v ^ 2 := by
  have hH : Hfun e (posMap e u v z) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) :=
    H_in_field_line_labels e u v z he he1 huv
  unfold psiFun
  rw [hH]
  ring
