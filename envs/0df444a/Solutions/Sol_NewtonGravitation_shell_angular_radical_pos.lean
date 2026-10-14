-- Prove2me | solution 1 for NewtonGravitation.shell_angular_radical_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:07:53.070974+00:00
-- url     : https://prove2.me/submissions/abccf304-45ec-4c3b-8543-80111d2c7b78

import Definitions.Def_NewtonGravitation_Defs
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NewtonGravitation

theorem solution (R r t : ℝ) (hR : 0 < R) (hr : 0 ≤ r)
    (hne : r ≠ R) (ht : t ≤ 1) :
    0 < R ^ 2 + r ^ 2 - 2 * R * r * t := by
  have hsub : R - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsq : 0 < (R - r) ^ 2 := sq_pos_of_ne_zero hsub
  have hterm : 0 ≤ R * r * (1 - t) :=
    mul_nonneg (mul_nonneg hR.le hr) (sub_nonneg.mpr ht)
  nlinarith [hterm]
