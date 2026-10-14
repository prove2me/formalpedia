-- Prove2me | solution 1 for NewtonGravitation.shell_angular_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:01:58.420557+00:00
-- url     : https://prove2.me/submissions/b4d70de4-6afa-4f48-88d4-e146597c70c8

import Definitions.Def_NewtonGravitation_Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open NewtonGravitation

theorem solution (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hne : r ≠ R) :
    ((R ^ 2 - r ^ 2) / |R - r| - |R - r|) / (4 * R ^ 2 * r) -
      ((R ^ 2 - r ^ 2) / |R + r| - |R + r|) / (4 * R ^ 2 * r) =
      if r < R then 1 / R ^ 2 else 0 := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hRp : R + r ≠ 0 := ne_of_gt (add_pos hR hr)
  by_cases hlt : r < R
  · have hRm : R - r ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
    rw [if_pos hlt, abs_of_pos (sub_pos.mpr hlt),
      abs_of_pos (add_pos hR hr)]
    field_simp [hR0, hr0, hRm, hRp]
    <;> ring
  · have hRlt : R < r := by
      rcases lt_or_gt_of_ne hne with hrlt | hrgt
      · exact False.elim (hlt hrlt)
      · exact hrgt
    have hRm : R - r ≠ 0 := ne_of_lt (sub_neg.mpr hRlt)
    rw [if_neg hlt, abs_of_neg (sub_neg.mpr hRlt),
      abs_of_pos (add_pos hR hr)]
    field_simp [hR0, hr0, hRm, hRp]
    <;> ring
