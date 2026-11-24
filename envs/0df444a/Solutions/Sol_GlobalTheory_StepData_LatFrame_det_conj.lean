-- Prove2me | solution 1 for GlobalTheory.StepData.LatFrame.det_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:36.415994+00:00
-- url     : https://prove2.me/submissions/c386129a-56e4-411f-adfa-ff08999a90ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_det_reGL
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply

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
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
open GlobalTheory.StepData.LatFrame
namespace GlobalTheory.StepData.LatFrame
theorem _root_.solution (F : LatFrame k ι Y) (g : GL ι k) :
    Matrix.GeneralLinearGroup.det (F.conj g) = Matrix.GeneralLinearGroup.det g := by
  rw [conj_apply, map_mul, map_mul, map_inv, det_reGL, mul_inv_cancel_comm]
end GlobalTheory.StepData.LatFrame
