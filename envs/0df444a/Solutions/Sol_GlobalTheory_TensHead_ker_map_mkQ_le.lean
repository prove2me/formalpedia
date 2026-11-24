-- Prove2me | solution 1 for GlobalTheory.TensHead.ker_map_mkQ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:38.278714+00:00
-- url     : https://prove2.me/submissions/9250ae80-5f40-4c64-99c8-22d734ff6ea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleTensorProductOperatorStableCountableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
namespace GlobalTheory.TensHead
theorem _root_.solution {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁]
    [Module ℂ V₁] (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) :
    LinearMap.ker (TensorProduct.map K₀.mkQ K₁.mkQ) ≤ tensKer K₀ K₁ := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_mkQ K₀) K₀.mkQ_surjective
    (LinearMap.exact_subtype_mkQ K₁) K₁.mkQ_surjective]
  refine sup_le ?_ ?_
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x k => exact Submodule.subset_span ⟨x, k, Or.inr k.2, by simp⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k y => exact Submodule.subset_span ⟨k, y, Or.inl k.2, by simp⟩
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
end GlobalTheory.TensHead
