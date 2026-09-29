-- Prove2me | solution 1 for Landreman3DEquilibria.psi_and_H_in_field_line_labels
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T19:18:23.726985+00:00
-- url     : https://prove2.me/submissions/d8f52c5b-ab95-4ef4-a8d1-e11bea80e0ea

import Mathlib
import Definitions.Def_landreman_vector_calculus
import Definitions.Def_landreman_integer_iota_family
import Theorems.Thm_Landreman3DEquilibria_H_in_field_line_labels
import Theorems.Thm_Landreman3DEquilibria_psi_in_field_line_labels

open Landreman3DEquilibria

theorem solution (e u v z : ℝ) (he : 0 < e) (he1 : e < 1)
    (huv : u ^ 2 + v ^ 2 < 1 / 4) :
    Hfun e (posMap e u v z) = 1 + 2 * e * u + 2 * (u ^ 2 + v ^ 2) ∧
      psiFun e (posMap e u v z) = (u + e / 2) ^ 2 + v ^ 2 := by
  exact ⟨H_in_field_line_labels e u v z he he1 huv,
         psi_in_field_line_labels e u v z he he1 huv⟩
