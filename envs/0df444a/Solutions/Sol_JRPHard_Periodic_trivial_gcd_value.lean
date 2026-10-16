-- Prove2me | solution 1 for JRPHard.Periodic.trivial_gcd_value
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:54:58.098911+00:00
-- url     : https://prove2.me/submissions/da9a51cf-759c-4861-96fb-f9dc815d307c

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 2.
theorem solution (M q : ℕ) (hq : 0 < q)
    (hg : Nat.gcd q M = 1 ∨ Nat.gcd q M = M) :
    (M : ℝ) ≤ obj4 M q := by
  rcases hg with hg | hg
  · simp only [obj4, hg, Nat.cast_one, div_one]
    linarith [Nat.cast_nonneg (α := ℝ) q]
  · have hmq : (M : ℝ) ≤ q := by
      have hh := Nat.gcd_le_left M hq
      rw [hg] at hh
      exact_mod_cast hh
    rw [obj4, hg]
    have hh : 0 ≤ (M : ℝ) / M := by positivity
    linarith
