-- Prove2me | solution 1 for GlobalTheory.ZetaLocal.order_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:25.430299+00:00
-- url     : https://prove2.me/submissions/7e57276a-da0f-428b-82e8-d0b77f018523

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtFractInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivRiemannZetaLocalZeroSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ZetaLocal
namespace GlobalTheory.ZetaLocal
theorem _root_.solution (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by
  unfold analyticOrderNatAt
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z)
    (z₀ := w) (by fun_prop) (by simp)
  exact congrArg _ this
end GlobalTheory.ZetaLocal
