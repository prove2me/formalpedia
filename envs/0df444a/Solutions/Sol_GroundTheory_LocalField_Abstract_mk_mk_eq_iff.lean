-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.mk_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:43.706946+00:00
-- url     : https://prove2.me/submissions/97146797-3257-4501-a165-c64f2af50240

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Theorems.Thm_GroundTheory_LocalField_Abstract_mk_mem_range_galRestrict_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]
omit [IsTopologicalGroup G] [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hLK' : L ≤ K') (hK'K : K' ≤ K) (a b : (K : Subgroup G)) :
    ((a : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
        _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((b : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (a : G)⁻¹ * b ∈ (K' : Subgroup G) := by
  rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    mk_mem_range_galRestrict_iff hLK' hK'K]
  simp
end GroundTheory.LocalField.Abstract
