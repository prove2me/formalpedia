-- Prove2me | solution 1 for MultiChoiceSecretary.Alg.combine_estimates
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:43:15.701988+00:00
-- url     : https://prove2.me/submissions/f2750cff-cac9-4e97-9fd4-a028a3713ae7

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting
set_option autoImplicit false

theorem solution (k : ℝ) (hk : 0 < k) :
    1 - 5 / Real.sqrt k <
      (1 - 5 / Real.sqrt (k / 2)) * (1 - 1 / (2 * Real.sqrt k)) * (1 / 2) +
        (1 / 2 - Real.sqrt (1 / k)) := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hr : 0 < Real.sqrt 2 := by positivity
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr3 : Real.sqrt 2 < 3 / 2 := by nlinarith
  set t := 1 / Real.sqrt k with htdef
  have ht : 0 < t := by positivity
  have h1 : 5 / Real.sqrt k = 5 * t := by rw [htdef]; ring
  have h2 : 5 / Real.sqrt (k / 2) = 5 * Real.sqrt 2 * t := by
    rw [Real.sqrt_div hk.le, htdef]; field_simp
  have h3 : 1 / (2 * Real.sqrt k) = t / 2 := by rw [htdef]; field_simp
  have h4 : Real.sqrt (1 / k) = t := by rw [htdef, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [h1, h2, h3, h4]
  nlinarith [mul_pos ht (show 0 < 15 / 4 - 5 / 2 * Real.sqrt 2 by linarith),
    mul_pos (mul_pos hr ht) ht]
