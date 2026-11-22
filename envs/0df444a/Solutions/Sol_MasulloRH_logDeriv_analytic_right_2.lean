-- Prove2me | solution 2 for MasulloRH.logDeriv_analytic_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:45:09.74798+00:00
-- url     : https://prove2.me/submissions/986c3437-bf04-402c-9110-3e6729334478
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis

set_option autoImplicit false

namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have ha : AnalyticAt ℂ riemannZeta s :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hs_one)
  have hne : riemannZeta s ≠ 0 := by
    intro hz
    have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hhalf := mathlib_riemannHypothesis s hz htriv hs_one
    linarith
  exact ha.deriv.div ha hne
