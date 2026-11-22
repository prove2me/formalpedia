-- Prove2me | solution 2 for MasulloRH.regularized_trace_scalar_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:11:34.719169+00:00
-- url     : https://prove2.me/submissions/561c83d2-701c-4306-aa81-440ab10b095a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_compensated_resolvent_kernel_pos
import Theorems.Thm_MasulloRH_compensated_resolvent_trace_tail_bound

open MasulloRH

theorem solution (α : ℝ) (hα : 0 < α) (hsmall : α < 1 / 2) :
    (zetaLogDeriv 3).re ≤ (regularizedTraceRHS α 3).re := by
  have hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k := by
    intro β γ T hβ0 hβ1 hγ
    exact compensated_resolvent_kernel_pos β γ T hβ0 hβ1 hγ
  have htail := compensated_resolvent_trace_tail_bound α hα hsmall hkernel
  have hfull := regularized_initial_identity_full_strip (3 : ℂ) (by norm_num)
  have hre : (regularizedTraceRHS (1 / 2) 3).re = (zetaLogDeriv 3).re :=
    congrArg Complex.re hfull
  nlinarith
