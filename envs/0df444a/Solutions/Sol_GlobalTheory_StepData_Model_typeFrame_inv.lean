-- Prove2me | solution 1 for GlobalTheory.StepData.Model.typeFrame_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:13:12.422879+00:00
-- url     : https://prove2.me/submissions/1b510059-3b8a-4fa4-aed0-f9e46717ae9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_Model_wt_ne_zero
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_val

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
open GlobalTheory GlobalTheory.StepData GlobalTheory.StepData.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData.Model
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) :
    ((typeFrame ϖ o).bas⁻¹).val = diagonal fun i => (wt ϖ i)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [typeFrame_val, diagonal_mul_diagonal, ← diagonal_one]
  congr; funext i; exact mul_inv_cancel₀ (wt_ne_zero ϖ i)
end GlobalTheory.StepData.Model
