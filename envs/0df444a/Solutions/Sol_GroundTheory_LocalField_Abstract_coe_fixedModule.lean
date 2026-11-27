-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_fixedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:31.453504+00:00
-- url     : https://prove2.me/submissions/05d8d9d9-ed8b-41bd-a5c5-4b2630aba5a0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Theorems.Thm_GroundTheory_LocalField_Abstract_mem_fixedModule

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
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable {A}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (H : Subgroup G) :
    (fixedModule A H : Set A) = MulAction.fixedPoints H A := by
  ext a
  simp only [SetLike.mem_coe, mem_fixedModule, MulAction.mem_fixedPoints, Subtype.forall,
    Subgroup.mk_smul]
end GroundTheory.LocalField.Abstract
