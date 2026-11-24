-- Prove2me | solution 1 for GlobalTheory.StepData.Model.coords_typeFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:48.90397+00:00
-- url     : https://prove2.me/submissions/96380345-d10c-41f8-b227-0881d1d21658

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_val
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_inv

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
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) (o' : ι' ≃ n' ⊕ Fin c')
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (i : ι) (j : ι') :
    (typeFrame ϖ o).coords (typeFrame ϖ o') x i j = (wt ϖ (o i))⁻¹ * x (o i) (o' j) * wt ϖ (o' j) := by
  rw [LatFrame.coords, typeFrame_val, typeFrame_inv, submatrix_apply, mul_diagonal, diagonal_mul]; rfl
end GlobalTheory.StepData.Model
