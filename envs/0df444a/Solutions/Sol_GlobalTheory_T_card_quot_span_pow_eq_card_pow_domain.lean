-- Prove2me | solution 1 for GlobalTheory.T.card_quot_span_pow_eq_card_pow_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:44:16.352585+00:00
-- url     : https://prove2.me/submissions/2eca607e-25a7-4a9e-926d-fd2f85c0488a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomainStatement
import Theorems.Thm_GlobalTheory_card_quot_span_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) → ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  first | exact @GlobalTheory.card_quot_span_pow | exact GlobalTheory.card_quot_span_pow | (intros; apply GlobalTheory.card_quot_span_pow <;> assumption)
end _root_.GlobalTheory.T
