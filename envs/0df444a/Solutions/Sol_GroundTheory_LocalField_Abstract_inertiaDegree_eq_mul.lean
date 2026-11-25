-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.inertiaDegree_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:40:11.631288+00:00
-- url     : https://prove2.me/submissions/dcc31d08-9e7e-4d54-aa2f-495bd9120d73

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_RelIndexSup
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_relInertiaDegree_top
import Theorems.Thm_GroundTheory_LocalField_Abstract_relInertiaDegree_mul

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
theorem _root_.solution (hd : Function.Surjective d) {K L : Subgroup G} (hLK : L ≤ K) :
    inertiaDegree d L = relInertiaDegree d K L * inertiaDegree d K := by
  rw [← relInertiaDegree_top hd, ← relInertiaDegree_top hd, relInertiaDegree_mul hLK le_top]
end GroundTheory.LocalField.Abstract
