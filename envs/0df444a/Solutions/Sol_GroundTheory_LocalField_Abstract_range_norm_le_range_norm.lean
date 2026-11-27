-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.range_norm_le_range_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:48:49.172001+00:00
-- url     : https://prove2.me/submissions/fbfdf48b-bfbf-475c-ae81-64796e470c7d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_norm

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
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
variable {K L M : Subgroup G}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hML : M ≤ L) (hLK : L ≤ K) [(L.subgroupOf K).FiniteIndex]
    [(M.subgroupOf L).FiniteIndex] [(M.subgroupOf K).FiniteIndex] :
    (norm A K M).range ≤ (norm A K L).range := by
  rintro _ ⟨a, rfl⟩
  exact ⟨norm A L M a, norm_norm hML hLK a⟩
end GroundTheory.LocalField.Abstract
