-- Prove2me | solution 1 for GlobalTheory.FibLine.Intg.continuous_qCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:51.252119+00:00
-- url     : https://prove2.me/submissions/41bb2d91-18bc-40d9-9d91-cd2208265465

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableProdQCoefMulFsDens
import Theorems.Thm_GlobalTheory_FibLine_Intg_continuous_lineVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.Intg
namespace GlobalTheory.FibLine.Intg
theorem _root_.solution (ab : Fin 2 × Fin 2) : Continuous fun x : ℂ => qCoef x ab := by
  unfold qCoef
  refine Continuous.div ((continuous_lineVec _).mul (Complex.continuous_conj.comp (continuous_lineVec _)))
    (Complex.continuous_ofReal.comp (by fun_prop)) fun x => ?_
  have hx : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
  exact_mod_cast hx.ne'
end GlobalTheory.FibLine.Intg
