-- Prove2me | solution 1 for OAI.PiExponent.rational_approximation_far_numerator_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-14T07:01:47.345983+00:00
-- url     : https://prove2.me/submissions/8d276693-6d90-4f0e-a06a-0fa1884d60f1

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-
Author: Alexander Richard Towell (queelius).
An elementary supporting bound for the Prove2Me π-exponent mission.
The target statement was supplied by the mission's existing decomposition.
-/

theorem solution (nu : ℝ) (hnu : 2 < nu)
    (p : ℤ) (q : ℕ) (hq : 2 ≤ q) (hlarge : 4 * (q : ℝ) < |(p : ℝ)|) :
    (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  have hqreal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have hpower : (q : ℝ) ^ (-nu) ≤ (q : ℝ) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
  have hquarter : (q : ℝ) ^ (-2 : ℝ) ≤ (1 : ℝ) / 4 := by
    rw [Real.rpow_neg hqpos.le, Real.rpow_two]
    have hsquare : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hsquare)
  have hratio : (4 : ℝ) < |(p : ℝ) / (q : ℝ)| := by
    rw [abs_div, abs_of_pos hqpos]
    exact (lt_div_iff₀ hqpos).mpr hlarge
  have hpi : Real.pi < (15 : ℝ) / 4 := by
    linarith [Real.pi_lt_d2]
  have hdist := abs_sub_abs_le_abs_sub ((p : ℝ) / (q : ℝ)) Real.pi
  rw [abs_of_pos Real.pi_pos, abs_sub_comm] at hdist
  linarith
