-- Prove2me | solution 4 for MasulloRH.logDeriv_on_strip_complement
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:16:47.648799+00:00
-- url     : https://prove2.me/submissions/b6cad09a-db4f-48ac-b69f-d9cd34562f55
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s :=
  by
  obtain ⟨hre, hs_one⟩ := hs
  have hhalf : (1 / 2 : ℝ) < s.re := by linarith
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have ha : AnalyticAt ℂ riemannZeta s :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hs_one)
  have hne : riemannZeta s ≠ 0 := by
    intro hz
    have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hren := congrArg Complex.re hn
      simp at hren
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hline := mathlib_riemannHypothesis s hz htriv hs_one
    linarith
  have hq : AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s :=
    ha.deriv.div ha hne
  exact hq
