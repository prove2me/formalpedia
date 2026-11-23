-- Prove2me | solution 2 for MasulloRH.compensated_resolvent_trace_tail_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:48.464768+00:00
-- url     : https://prove2.me/submissions/ea41e67c-ff70-4812-9fcf-890d0c440ebd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_single_resolvent_test
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

open MasulloRH

theorem solution
    (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2)
    (hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    0 ≤ (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re :=
  by
    have hstrip : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
      riemannHypothesis_iff_zeros_in_strip_on_line.mp mathlib_riemannHypothesis
    refine sub_nonneg.mpr ((MasulloRH.single_resolvent_test α).mpr fun ρ => ?_)
    rw [hstrip ρ.val ρ.2.1 ρ.2.2.1 ρ.2.2.2.1, sub_self, abs_zero]
    exact hα
