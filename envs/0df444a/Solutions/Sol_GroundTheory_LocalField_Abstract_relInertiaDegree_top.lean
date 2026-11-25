-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.relInertiaDegree_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:10.213002+00:00
-- url     : https://prove2.me/submissions/95dd3f53-dcb6-46e8-89aa-ad75ed8ea17e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G]
variable (d : G →* Multiplicative ℤ̂)
variable {d}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hd : Function.Surjective d) (K : Subgroup G) :
    relInertiaDegree d ⊤ K = inertiaDegree d K := by
  rw [relInertiaDegree, inertiaDegree, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective d hd, Subgroup.relIndex_top_right]
end GroundTheory.LocalField.Abstract
