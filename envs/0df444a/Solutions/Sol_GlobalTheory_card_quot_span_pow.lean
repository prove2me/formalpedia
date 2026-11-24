-- Prove2me | solution 1 for GlobalTheory.card_quot_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:34:55.387636+00:00
-- url     : https://prove2.me/submissions/862424a2-5299-41d7-93fd-351d744497cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomain
import Theorems.Thm_GlobalTheory_card_quot_span_pow_succ_eq_mul_domain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) →
      ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  intro O _ _ t ht _ r
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    rw [card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]
end GlobalTheory
