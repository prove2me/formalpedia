-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.relIndex_sup_of_le_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:09.266291+00:00
-- url     : https://prove2.me/submissions/3b31fab2-19c8-4c72-b0dc-c071ab2c2301

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_P2M_GroundTheory_Variant__N1_relIndex_sup_of_le_normalizer_7514b13ff881


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
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    H.relIndex (H ⊔ N) = H.relIndex N :=
  _root_.GroundTheory.Variant₂.N1.relIndex_sup_of_le_normalizer hLE
end GroundTheory.LocalField.Abstract
