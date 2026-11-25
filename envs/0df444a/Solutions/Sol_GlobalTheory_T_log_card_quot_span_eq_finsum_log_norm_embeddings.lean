-- Prove2me | solution 1 for GlobalTheory.T.log_card_quot_span_eq_finsum_log_norm_embeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:22.467152+00:00
-- url     : https://prove2.me/submissions/b23a2343-92b4-4633-bc7a-59077a4dcd13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddingsStatement
import Theorems.Thm_GlobalTheory_IndexNormEmb_log_card_quot_span_eq_finsum_log_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Module.Finite ℤ B] (b : B), b ≠ 0 → Finite (B ⧸ Ideal.span {b}) ∧ Real.log (Nat.card (B ⧸ Ideal.span {b})) = ∑ᶠ τ : B →+* ℂ, Real.log ‖τ b‖ := by
  first | exact @GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | exact GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm | (intros; apply GlobalTheory.IndexNormEmb.log_card_quot_span_eq_finsum_log_norm <;> assumption)
end _root_.GlobalTheory.T
