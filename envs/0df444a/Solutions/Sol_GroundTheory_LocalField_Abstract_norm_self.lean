-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.norm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:49.966858+00:00
-- url     : https://prove2.me/submissions/46d87ea1-bcf7-4fdd-8d1e-ad5a72eecfd2

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_UniqueQuotientSubgroupOfSelf
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm


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
variable (K : Subgroup G)
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution : norm A K K = MonoidHom.id (fixedModule A K) := by
  refine MonoidHom.ext fun a => Subtype.ext ?_
  rw [coe_norm, finprod_unique]
  show ((1 : K) : G) • (a : A) = a
  simp
end GroundTheory.LocalField.Abstract
