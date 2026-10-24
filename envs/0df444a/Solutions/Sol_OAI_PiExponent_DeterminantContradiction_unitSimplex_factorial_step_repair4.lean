-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplex_factorial_step_repair4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:53:37.132652+00:00
-- url     : https://prove2.me/submissions/07cf2bbf-ba6e-4fbb-87f3-9c131957fc62

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

theorem solution (n : Nat) :
    (1 / (Nat.factorial n : Real)) * (1 / (n + 1 : Real)) =
      1 / (Nat.factorial (n + 1) : Real) := by
  rw [Nat.factorial_succ]
  push_cast
  simp [div_eq_mul_inv, mul_inv_rev]