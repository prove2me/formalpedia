-- Prove2me | solution 1 for GlobalTheory.T.logDeriv_riemannZeta_local_zero_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:13:20.22703+00:00
-- url     : https://prove2.me/submissions/dedee886-c9db-498e-9740-44c556b63660

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSumStatement
import Theorems.Thm_GlobalTheory_ZetaLocal_logDeriv_riemannZeta_local


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  first | exact @GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | exact GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local | (intros; apply GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local <;> assumption)
end _root_.GlobalTheory.T
