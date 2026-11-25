-- Prove2me | solution 1 for GlobalTheory.T.neg_re_logDeriv_principalLFunction_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:32.945526+00:00
-- url     : https://prove2.me/submissions/2dff31f3-e402-41af-9075-cb0a016fb59b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Theorems.Thm_GlobalTheory_PrincipalLogDeriv_neg_re_logDeriv_le


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | exact GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | (intros; apply GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le <;> assumption)
end _root_.GlobalTheory.T
