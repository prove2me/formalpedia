-- Prove2me | solution 1 for GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:32.610257+00:00
-- url     : https://prove2.me/submissions/429da478-3cd1-4f26-a0b1-615977d9915d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegularStatement
import Theorems.Thm_GlobalTheory_card_fixedBy_quotient_eq_relIndex_of_pRegular


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
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  first | exact @GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | exact GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular | (intros; apply GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular <;> assumption)
end _root_.GlobalTheory.T
