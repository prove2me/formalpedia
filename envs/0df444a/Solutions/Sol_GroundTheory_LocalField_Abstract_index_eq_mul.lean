-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.index_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:37.085096+00:00
-- url     : https://prove2.me/submissions/fad27c6d-60f5-4d8f-ba26-d2107815a2ad

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_relRamificationIndex_top
import Theorems.Thm_GroundTheory_LocalField_Abstract_relInertiaDegree_top
import Theorems.Thm_GroundTheory_LocalField_Abstract_relIndex_eq_mul

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
    K.index = ramificationIndex d K * inertiaDegree d K := by
  rw [← relRamificationIndex_top, ← relInertiaDegree_top hd, ← relIndex_eq_mul le_top,
    Subgroup.relIndex_top_right]
end GroundTheory.LocalField.Abstract
