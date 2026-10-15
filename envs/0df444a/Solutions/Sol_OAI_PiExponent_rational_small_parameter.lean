-- Prove2me | solution 1 for OAI.PiExponent.rational_small_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:06:45.009051+00:00
-- url     : https://prove2.me/submissions/22c789dc-371b-46ce-bf75-715cac6173c9

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ q : ℚ,
      0 < (q : ℝ) ∧
      (q : ℝ) < min (1 / 4 : ℝ) (3 * (nu - 2) / (4 * (nu - 1))) := by
  have hnum : 0 < nu - 2 := by linarith
  have hden : 0 < nu - 1 := by linarith
  have hfrac : 0 < 3 * (nu - 2) / (4 * (nu - 1)) := by positivity
  have hbound : 0 < min (1 / 4 : ℝ) (3 * (nu - 2) / (4 * (nu - 1))) :=
    lt_min (by positivity) hfrac
  obtain ⟨q, hq0, hqbound⟩ := exists_rat_btwn hbound
  exact ⟨q, hq0, hqbound⟩