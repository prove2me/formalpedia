-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.relInertiaDegree_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:06.788879+00:00
-- url     : https://prove2.me/submissions/8c630666-86cb-4eda-b5c3-0c4b75cbe5cc

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
theorem _root_.solution {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relInertiaDegree d L M * relInertiaDegree d K L = relInertiaDegree d K M :=
  Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_mono hML) (Subgroup.map_mono hLK)
end GroundTheory.LocalField.Abstract
