-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.binomial_choose_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:55:41.921835+00:00
-- url     : https://prove2.me/submissions/40866825-b7e4-424f-8e3e-89da27b1cafa

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

theorem solution (n k : ℕ) :
    ((n.choose k : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) * Real.log 2) := by
  have hchoose : ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast Nat.choose_le_two_pow n k
  calc
    ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := hchoose
    _ = Real.exp ((n : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]