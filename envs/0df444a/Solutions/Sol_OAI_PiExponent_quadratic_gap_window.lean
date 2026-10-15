-- Prove2me | solution 1 for OAI.PiExponent.quadratic_gap_window
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:51:18.699947+00:00
-- url     : https://prove2.me/submissions/74fe5128-8de1-4ca8-9896-7b2fa3a2d0b3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Theorems.Thm_OAI_PiExponent_rational_small_parameter
import Theorems.Thm_OAI_PiExponent_window_from_small_parameter

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ (theta : ℚ) (A eta : ℝ),
      0 < theta ∧ theta < 1 ∧
      0 < A ∧ A < 1 ∧ 0 < eta ∧ eta < 1 ∧
      A ^ 2 < (theta : ℝ) ∧
      0 < nu * (A * (1 - eta) - (theta : ℝ)) -
        (1 - (theta : ℝ)) := by
  obtain ⟨q, hqpos, hqsmall⟩ :=
    OAI.PiExponent.rational_small_parameter nu hnu
  obtain ⟨theta, A, eta, _, _, _, htheta_pos, htheta_lt,
      hA_pos, hA_lt, heta_pos, heta_lt, hsq, hslack⟩ :=
    OAI.PiExponent.window_from_small_parameter nu hnu q hqpos hqsmall
  exact ⟨theta, A, eta, htheta_pos, htheta_lt, hA_pos, hA_lt,
    heta_pos, heta_lt, hsq, hslack⟩