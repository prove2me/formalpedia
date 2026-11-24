-- Prove2me | solution 1 for GlobalTheory.DCIndex.card_inf_subgroupOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:00.118815+00:00
-- url     : https://prove2.me/submissions/314348ed-5a2b-4dae-90c9-0c2b517f2ff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetCardDivCardInfCommutativeSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
open GlobalTheory GlobalTheory.DCIndex
namespace GlobalTheory.DCIndex
theorem _root_.solution {G : Type} [Group G] (T H U : Subgroup G) (hUT : U ≤ T) :
    Nat.card (H.subgroupOf T ⊓ U.subgroupOf T : Subgroup T) = Nat.card (H ⊓ U : Subgroup G) := by
  have he : H.subgroupOf T ⊓ U.subgroupOf T = (H ⊓ U).subgroupOf T := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [he]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUT)).toEquiv
end GlobalTheory.DCIndex
