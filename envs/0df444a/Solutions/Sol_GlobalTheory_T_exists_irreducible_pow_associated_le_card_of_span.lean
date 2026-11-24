-- Prove2me | solution 1 for GlobalTheory.T.exists_irreducible_pow_associated_le_card_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:00.011451+00:00
-- url     : https://prove2.me/submissions/1231c7d3-57e5-47f4-afe3-76530c3c354b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpan
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RamificationLeCardOfSpanStatement
import Theorems.Thm_GlobalTheory_ramification_le_card_of_span


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
theorem _root_.solution : ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' → IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''), (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F), (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) → ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧ Associated (Subring.inclusion h π) (ϖ ^ e) := by
  first | exact @GlobalTheory.ramification_le_card_of_span | exact GlobalTheory.ramification_le_card_of_span | (intros; apply GlobalTheory.ramification_le_card_of_span <;> assumption)
end _root_.GlobalTheory.T
