-- Prove2me | solution 1 for MasulloRH.logDeriv_analytic_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-11-20T21:39:26.651813+00:00
-- url     : https://prove2.me/submissions/2652d424-147d-4320-ab0e-1528f0aea978
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_logDeriv_on_strip_complement
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open MasulloRH

/-- Any point right of the critical line lies beyond a smaller positive strip. -/
theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by
  let α : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4)
  have hα : 0 < α := by
    dsimp [α]
    exact lt_min (by linarith) (by norm_num)
  have hsmall : α < 1 / 2 := by
    have hle : α ≤ 1 / 4 := min_le_right _ _
    linarith
  have hdomain : InTraceContinuationDomain α s := by
    refine ⟨?_, hs_one⟩
    have hle : α ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  exact logDeriv_on_strip_complement α hα hsmall s hdomain
