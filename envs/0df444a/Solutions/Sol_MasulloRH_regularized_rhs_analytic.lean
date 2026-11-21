-- Prove2me | solution 1 for MasulloRH.regularized_rhs_analytic
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-20T21:37:08.657487+00:00
-- url     : https://prove2.me/submissions/6cdc5216-a495-4609-a13e-794c99c293d3

import Theorems.Thm_MasulloRH_regularized_arch_analytic
import Theorems.Thm_MasulloRH_regularized_spectral_analytic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MasulloRH

/-- Holomorphy of the explicit pieces gives holomorphy of their signed sum. -/
theorem solution (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ (regularizedTraceRHS α) s := by
  have hsre : (1 / 2 : ℝ) < s.re := by linarith [hs.1]
  have hs0 : s ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.zero_re] at hre
    linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.2
  have ha := regularized_arch_analytic s hsre
  have hsp := (regularized_spectral_analytic α hα hαsmall s hs.1).2
  have hp : AnalyticAt ℂ regularizedPolar s := by
    unfold regularizedPolar
    fun_prop (disch := assumption)
  unfold regularizedTraceRHS
  fun_prop
