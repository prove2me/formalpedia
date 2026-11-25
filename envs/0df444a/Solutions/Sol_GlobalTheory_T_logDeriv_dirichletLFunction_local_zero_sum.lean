-- Prove2me | solution 1 for GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:18.636818+00:00
-- url     : https://prove2.me/submissions/1c793767-2516-4387-9485-f61f3c8e123d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Theorems.Thm_GlobalTheory_LLocal_logDeriv_LFunction_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
end _root_.GlobalTheory.T
