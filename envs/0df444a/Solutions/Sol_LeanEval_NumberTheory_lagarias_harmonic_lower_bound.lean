-- Prove2me | solution 1 for LeanEval.NumberTheory.lagarias_harmonic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:29:09.228809+00:00
-- url     : https://prove2.me/submissions/571c7ad0-9769-4779-b770-583dd97ea8ee

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

open scoped ArithmeticFunction.sigma

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 3 ≤ n) :
    Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
      Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hgamma : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hmain : Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log (n : ℝ) := by
    simpa [Real.eulerMascheroniSeq', hn0] using Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hH : Real.log (n : ℝ) ≤ (harmonic n : ℝ) := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log (Real.log (n : ℝ)) ≤ Real.log (harmonic n : ℝ) :=
    Real.log_le_log hlogpos hH
  have hlogone : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnpos).2 (by linarith [Real.exp_one_lt_three])
  have hloglog : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg hlogone.le
  have hexp : Real.exp Real.eulerMascheroniConstant * (n : ℝ) ≤ Real.exp (harmonic n : ℝ) := by
    calc
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) =
          Real.exp (Real.eulerMascheroniConstant + Real.log (n : ℝ)) := by
            rw [Real.exp_add, Real.exp_log hnpos]
      _ ≤ Real.exp (harmonic n : ℝ) := Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hexp hlog hloglog (Real.exp_pos _).le
