-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.exp_bound_of_ceil_log
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:51:10.892641+00:00
-- url     : https://prove2.me/submissions/9905dfe3-0579-461b-9079-25b12815fda1

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Tactic.Linarith

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (q K : ℕ) (hnu : 0 ≤ nu)
    (hq : 2 ≤ q) (hK : 1 ≤ K) :
    2 * (K : ℝ) * (q : ℝ) ^ (-nu) ≤
      Real.exp
        (Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    have hq_ge : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hA_pos : (0 : ℝ) < 2 * (K : ℝ) := by
    have hK_ge : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    positivity
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by
    have hq_one : (1 : ℕ) ≤ q := le_trans (by decide : (1 : ℕ) ≤ 2) hq
    exact_mod_cast hq_one
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq_ge_one
  have hceil :
      (Nat.ceil (Real.log (q : ℝ)) : ℝ) ≤ Real.log (q : ℝ) + 1 :=
    (Nat.ceil_lt_add_one hlog_nonneg).le
  have hceil_mul := mul_le_mul_of_nonneg_left hceil hnu
  have hexp :
      Real.log (2 * (K : ℝ)) + Real.log (q : ℝ) * (-nu) ≤
        Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ) := by
    nlinarith
  rw [Real.rpow_def_of_pos hq_pos]
  calc
    2 * (K : ℝ) * Real.exp (Real.log (q : ℝ) * (-nu)) =
        Real.exp (Real.log (2 * (K : ℝ)) + Real.log (q : ℝ) * (-nu)) := by
          rw [Real.exp_add, Real.exp_log hA_pos]
    _ ≤ Real.exp
        (Real.log (2 * (K : ℝ)) + nu -
          nu * (Nat.ceil (Real.log (q : ℝ)) : ℝ)) :=
      Real.exp_le_exp.mpr hexp
