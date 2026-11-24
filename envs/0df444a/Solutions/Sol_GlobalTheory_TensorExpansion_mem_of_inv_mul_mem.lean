-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.mem_of_inv_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:42.293927+00:00
-- url     : https://prove2.me/submissions/08569481-b5b5-49a1-b9b6-22b0c36c12cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Theorems.Thm_GlobalTheory_TensorExpansion_unitsPowInv_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
open GlobalTheory GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TensorExpansion
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by
  have hx : x = (ϖ : k) ^ e * ((((ϖ ^ e)⁻¹ : kˣ) : k) * x) := by
    rw [unitsPowInv_val, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  rw [hx]
  exact mul_mem (pow_mem hϖ.mem _) h
end GlobalTheory.TensorExpansion
