-- Prove2me | solution 1 for GlobalTheory.SliceOp.contDiff_qOp_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:50.830733+00:00
-- url     : https://prove2.me/submissions/3e03e8e1-148d-4503-ad9c-f68cfac8ccb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperator
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
import Theorems.Thm_GlobalTheory_T_partial_operator_fderiv_formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SliceSchwartz.sliceR_apply



set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']
namespace GlobalTheory.SliceOp
theorem _root_.solution (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ), ContDiff ℝ n (qOp P f) := by
  induction n with
  | zero => intro P f; exact contDiff_zero.2 (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).1.continuous
  | succ n ih =>
    intro P f
    obtain ⟨hd, hf⟩ := GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv_apply]
    refine ⟨hd, by simp, fun v => ?_⟩
    have : (fun s => fderiv ℝ (qOp P f) s v) = fun s =>
        qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s :=
      funext fun s => hf s v
    rw [this]
    exact (ih _ _).add (ih _ _)
end GlobalTheory.SliceOp
