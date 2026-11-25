-- Prove2me | solution 1 for GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:16.490427+00:00
-- url     : https://prove2.me/submissions/b3f4c0de-77a6-42e3-b535-2197fe1f8be5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedBy
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedByStatement
import Theorems.Thm_P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  first | exact @GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | exact GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ | (intros; apply GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂ <;> assumption)
end _root_.GlobalTheory.T
