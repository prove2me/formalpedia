-- Prove2me | solution 1 for GlobalTheory.DCIndex.card_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:12.793806+00:00
-- url     : https://prove2.me/submissions/1772d407-62b5-4778-8129-cfd3c66fbbc7

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
variable {A : Type} [Group A]
namespace GlobalTheory.DCIndex
theorem _root_.solution (h u c : Subgroup A) (huc : u ≤ c) :
    (h ⊓ u).relIndex (h ⊓ c) * Nat.card (h ⊓ u : Subgroup A) = Nat.card (h ⊓ c : Subgroup A) := by
  have hle : h ⊓ u ≤ h ⊓ c := inf_le_inf_left h huc
  have := Subgroup.card_mul_index ((h ⊓ u).subgroupOf (h ⊓ c))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at this
  rw [Subgroup.relIndex, mul_comm, this]
end GlobalTheory.DCIndex
