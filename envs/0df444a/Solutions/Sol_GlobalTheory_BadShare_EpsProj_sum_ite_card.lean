-- Prove2me | solution 1 for GlobalTheory.BadShare.EpsProj.sum_ite_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:37.397852+00:00
-- url     : https://prove2.me/submissions/ae653fd0-5c4c-45a1-bb00-417feee4fd35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SubgroupCharacterIdempotentProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.EpsProj
variable {G : Type} [Group G] [Fintype G] {S : G → Prop} {χ : G → ℂ}
omit [Group G]
namespace GlobalTheory.BadShare.EpsProj
theorem _root_.solution : ∑ y, (if S y then (1 : ℂ) else 0) = (Nat.card {u // S u} : ℂ) := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
end GlobalTheory.BadShare.EpsProj
