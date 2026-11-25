-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.relRamificationIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:08.88531+00:00
-- url     : https://prove2.me/submissions/f9aef711-fc6d-40ba-b550-8a968d3c9c26

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
    relRamificationIndex d L M * relRamificationIndex d K L = relRamificationIndex d K M := by
  unfold relRamificationIndex
  have h := Subgroup.relIndex_inf_mul_relIndex M L (d.ker ⊓ K)
  have h1 : L ⊓ (d.ker ⊓ K) = d.ker ⊓ L := by
    rw [inf_comm d.ker K, ← inf_assoc, inf_eq_left.2 hLK, inf_comm]
  rw [h1, inf_eq_left.2 hML] at h
  exact h
end GroundTheory.LocalField.Abstract
