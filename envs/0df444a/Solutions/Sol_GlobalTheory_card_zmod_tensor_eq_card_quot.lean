-- Prove2me | solution 1 for GlobalTheory.card_zmod_tensor_eq_card_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:14.628214+00:00
-- url     : https://prove2.me/submissions/ebe619c4-ad69-417d-94a1-3c30ae16e5e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
import Theorems.Thm_GlobalTheory_ideal_span_natCast_smul_top_eq_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    Nat.card (TensorProduct ℤ (ZMod p) M) =
      Nat.card (M ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M))) := by
  rw [← Nat.card_congr ((intQuotSpanNatLinearEquivZMod p).rTensor M).toEquiv,
    Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {(p : ℤ)})).toEquiv,
    ideal_span_natCast_smul_top_eq_range]
end GlobalTheory
