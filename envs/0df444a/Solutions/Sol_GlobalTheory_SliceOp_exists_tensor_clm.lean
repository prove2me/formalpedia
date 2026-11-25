-- Prove2me | solution 1 for GlobalTheory.SliceOp.exists_tensor_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:48.21239+00:00
-- url     : https://prove2.me/submissions/df252351-5ae7-4f48-8d04-d1f47fc572c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorFderivFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialOperatorSchwartzSeminormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivativeBoundByPartialsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperator
import Theorems.Thm_GlobalTheory_SliceOp_contDiff_qOp
import Theorems.Thm_GlobalTheory_SliceOp_decay_qOp
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceRL_apply
import Theorems.Thm_GlobalTheory_SliceSchwartz_sliceR_apply
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
open GlobalTheory.SliceOp
namespace GlobalTheory.SliceOp
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f => qOp P f) ?_ ?_ ?_ ?_, fun f s => rfl⟩
  · intro f g s
    simp only [qOp, ← sliceRL_apply, map_add, SchwartzMap.add_apply]
  · intro a f s
    simp only [qOp, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
  · intro f; exact contDiff_qOp P f
  · rintro ⟨k, n⟩; exact decay_qOp n P k
end GlobalTheory.SliceOp
