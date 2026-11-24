-- Prove2me | solution 1 for GlobalTheory.StepData.LatFrame.coords_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:08.026305+00:00
-- url     : https://prove2.me/submissions/92add03a-772d-42db-a950-8bdcac303d7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_reGL_val
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
theorem _root_.solution (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (h : GL ι k) (g : GL ι' k) (x : Matrix Y Y' k) :
    F.coords F' ((F.conj h).val * x * (F'.conj g).val) = h.val * F.coords F' x * g.val := by
  have e : (F.bas⁻¹).val * ((F.conj h).val * x * (F'.conj g).val) * F'.bas.val =
      (reGL F.ord h).val * ((F.bas⁻¹).val * x * F'.bas.val) * (reGL F'.ord g).val := by
    simp only [conj_apply, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold coords
  rw [e, ← submatrix_mul_equiv _ _ _ F'.ord, ← submatrix_mul_equiv _ _ _ F.ord]
  simp [reGL_val]
end GlobalTheory.StepData.LatFrame
