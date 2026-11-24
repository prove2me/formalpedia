-- Prove2me | solution 1 for GlobalTheory.StepData.det_reGL
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:04:14.012664+00:00
-- url     : https://prove2.me/submissions/b4024d18-0be7-4426-a4f6-a9949ba94309
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_reGL_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {a b t : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution (e : a ≃ b) (g : GL a k) :
    Matrix.GeneralLinearGroup.det (reGL e g) = Matrix.GeneralLinearGroup.det g :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, reGL_val])
end GlobalTheory.StepData
