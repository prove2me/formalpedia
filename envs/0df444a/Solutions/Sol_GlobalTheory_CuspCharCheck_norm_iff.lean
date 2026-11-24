-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.norm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:05:37.437825+00:00
-- url     : https://prove2.me/submissions/41085c20-2571-4a11-9dd4-eb7bae5457b0

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_BadShare_ZCalc_character_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution [Fintype G] (V : FDRep ℂ G) :
    (∑ x, V.character x * star (V.character x)) = (Fintype.card G : ℂ) ↔ Simple V := by
  rw [FDRep.simple_iff_char_is_norm_one, Nat.card_eq_fintype_card]
  simp only [GlobalTheory.BadShare.ZCalc.character_inv, starRingEnd_apply]
end GlobalTheory.CuspCharCheck
