-- Prove2me | solution 1 for GlobalTheory.T.schwartz_tensor_right_operator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:24:39.42218+00:00
-- url     : https://prove2.me/submissions/09772d9d-a41a-47ed-a590-d17e74b11f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTensorRightOperatorStatement
import Theorems.Thm_GlobalTheory_SliceOp_exists_tensor_clm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  first | exact @GlobalTheory.SliceOp.exists_tensor_clm | exact GlobalTheory.SliceOp.exists_tensor_clm | (intros; apply GlobalTheory.SliceOp.exists_tensor_clm <;> assumption)
end _root_.GlobalTheory.T
