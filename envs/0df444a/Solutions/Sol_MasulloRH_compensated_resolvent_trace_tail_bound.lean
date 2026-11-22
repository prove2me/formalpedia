-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_trace_tail_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:19:25.341355+00:00
-- url     : https://prove2.me/submissions/c1b3e051-5359-4cf2-9251-29bed210a9a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_compensated_resolvent_defect_series

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
    0 ≤ (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re := by
  rcases compensated_resolvent_defect_series α hα hsmall hkernel with ⟨f, hf, _hs, hEq⟩
  rw [hEq]
  have hsum : 0 ≤ ∑' ρ : ZetaZerosInTraceStrip (1 / 2), f ρ :=
    tsum_nonneg hf
  exact hsum
