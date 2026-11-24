-- Prove2me | solution 1 for GlobalTheory.T.partial_operator_fderiv_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:06.206399+00:00
-- url     : https://prove2.me/submissions/5fc3ff57-6408-4684-a354-78834f8c9f63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormula
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormulaStatement
import Theorems.Thm_GlobalTheory_SliceOp_differentiable_qOp_and_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  first | exact @GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | exact GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | (intros; apply GlobalTheory.SliceOp.differentiable_qOp_and_fderiv <;> assumption)
end _root_.GlobalTheory.T
