-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.resMk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:27:43.211392+00:00
-- url     : https://prove2.me/submissions/c5f066a9-1d08-4657-a59a-5fda8386c34b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
import Theorems.Thm_GlobalTheory_TensorExpansion_unitsPowInv_val
import Theorems.Thm_GlobalTheory_SplitFlip_IsUnif_maximalIdeal_eq


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
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  have h0 : (ϖ : k) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    unitsPowInv_val]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (a : k) - b = (ϖ : k) ^ e * c := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [h1, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]
end GlobalTheory.TensorExpansion
