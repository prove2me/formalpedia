-- Prove2me | solution 2 for OAI.PiExponent.rational_approximation_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T09:12:45.90733+00:00
-- url     : https://prove2.me/submissions/0caa370a-9846-4f6c-992a-71c7fd9f6bdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_local_bound
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨Q, hQ, hlocal⟩ := OAI.PiExponent.rational_approximation_local_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro p q hq
  have hq2 : 2 ≤ q := le_trans hQ hq
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  by_cases hp : |(p : ℝ)| ≤ 4 * (q : ℝ)
  · exact hlocal p q hq hp
  · have hpgt : 4 * (q : ℝ) < |(p : ℝ)| := lt_of_not_ge hp
    have hfar : (4 : ℝ) < |(p : ℝ) / (q : ℝ)| := by
      rw [abs_div, abs_of_pos hqpos]
      exact (lt_div_iff₀ hqpos).2 (by linarith)
    have hdist : (1 / 4 : ℝ) < |Real.pi - (p : ℝ) / (q : ℝ)| := by
      have hrev := abs_sub_abs_le_abs_sub ((p : ℝ) / (q : ℝ)) Real.pi
      rw [abs_of_pos Real.pi_pos, abs_sub_comm] at hrev
      have hpi : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
      linarith
    have hsmall : (q : ℝ) ^ (-nu) ≤ (1 / 4 : ℝ) := by
      calc
        (q : ℝ) ^ (-nu) ≤ (q : ℝ) ^ (-2 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ q)
          linarith
        _ ≤ (2 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hqR (by norm_num)
        _ = (1 / 4 : ℝ) := by norm_num
    exact le_of_lt (lt_of_le_of_lt hsmall hdist)
