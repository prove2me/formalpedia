-- Prove2me | solution 1 for GlobalTheory.T.doubleCoset_card_div_card_inf_commutative_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:19.931806+00:00
-- url     : https://prove2.me/submissions/e5ce66e6-babf-4285-88ca-3c2132e169ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroupStatement
import Theorems.Thm_GlobalTheory_DCIndex_index_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] (T H U C : Subgroup G), (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) → U ≤ C → C ≤ T → U.relIndex C ≠ 0 → (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((U.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ U : Subgroup G) : ℂ) = (U.relIndex C : ℂ) * (Nat.card (DoubleCoset.Quotient ((H.subgroupOf T : Subgroup T) : Set T) ((C.subgroupOf T : Subgroup T) : Set T)) : ℂ) / (Nat.card (H ⊓ C : Subgroup G) : ℂ) := by
  first | exact @GlobalTheory.DCIndex.index_identity | exact GlobalTheory.DCIndex.index_identity | (intros; apply GlobalTheory.DCIndex.index_identity <;> assumption)
end _root_.GlobalTheory.T
