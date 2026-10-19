-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.rowScalar_weighted_binomial_bound_single
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:05:40.319212+00:00
-- url     : https://prove2.me/submissions/7859a3ad-29ff-40a5-ad4c-cc2ea0961d65

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_choose_term_le_three_pow
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_choose_weighted_row_le_four_pow

open scoped BigOperators

theorem solution
    (a b : ℕ) (e : Fin (a - b + 1)) :
    (((a.choose b * (a - b).choose (e : ℕ) : ℕ) : ℝ) *
      (2 : ℝ) ^ (e : ℕ)) ≤ (4 : ℝ) ^ a := by
  have he : (e : ℕ) ≤ a - b := by
    exact Nat.lt_succ_iff.mp e.isLt
  have hterm : (a - b).choose (e : ℕ) * 2 ^ (e : ℕ) ≤ 3 ^ (a - b) :=
    OAI.PiExponent.LiteralAnalytic.weighted_choose_term_le_three_pow
      (a - b) (e : ℕ) he
  have hrow : a.choose b * 3 ^ (a - b) ≤ 4 ^ a :=
    OAI.PiExponent.LiteralAnalytic.choose_weighted_row_le_four_pow a b
  have hnat : a.choose b * ((a - b).choose (e : ℕ) * 2 ^ (e : ℕ)) ≤ 4 ^ a := by
    exact (Nat.mul_le_mul_left (a.choose b) hterm).trans hrow
  exact_mod_cast (by simpa [Nat.mul_assoc] using hnat)