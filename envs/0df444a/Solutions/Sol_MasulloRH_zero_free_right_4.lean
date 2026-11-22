-- Prove2me | solution 4 for MasulloRH.zero_free_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:31:53.442944+00:00
-- url     : https://prove2.me/submissions/1cb479bf-ae47-441b-8023-7ea59a868323
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_trace_formula_rational
import Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_zero_free
import Mathlib.NumberTheory.LSeries.Nonvanishing

set_option autoImplicit false

theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · have hα : 0 < s.re - 1 / 2 := by linarith
    exact MasulloAudit.trace_formula_rational_fixed_window_zero_free (s.re - 1 / 2) hα
      (fun φ hφ => MasulloRH.trace_formula_rational (s.re - 1 / 2) hα φ hφ) s
      (by linarith) h1
