-- Prove2me | solution 1 for GlobalTheory.TensHead.quotOp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:39.691189+00:00
-- url     : https://prove2.me/submissions/8c615292-3292-4b01-a063-9a9e5f32dc08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel
import Theorems.Thm_GlobalTheory_TensHead_quotOp_mk

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.TensHead
theorem _root_.solution (N : Submodule ℂ V) (f₁ f₂ : Module.End ℂ V) (h₁ : ∀ x ∈ N, f₁ x ∈ N)
    (h₂ : ∀ x ∈ N, f₂ x ∈ N) : quotOp N f₁ * quotOp N f₂ = quotOp N (f₁ * f₂) := by
  have h₁₂ : ∀ x ∈ N, (f₁ * f₂) x ∈ N := fun x hx => h₁ _ (h₂ x hx)
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.comp_apply, Module.End.mul_apply]
  rw [quotOp_mk N f₂ h₂, quotOp_mk N f₁ h₁, quotOp_mk N _ h₁₂, Module.End.mul_apply]
end GlobalTheory.TensHead
