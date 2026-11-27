-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.augmentation_le_map_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:29.178212+00:00
-- url     : https://prove2.me/submissions/e82f8b64-7127-4bb2-bf88-eb5caf43d7f1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule_of_normal
import Theorems.Thm_GroundTheory_LocalField_Abstract_norm_smul

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
variable (K L : Subgroup G)
variable {A K L}
variable (A K L)
variable [(L.subgroupOf K).FiniteIndex]
variable {A K L}
variable (A K L)
variable {A K L}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (hLK : L ≤ K) [(L.subgroupOf K).Normal] :
    augmentation A K L ≤ (norm A K L).ker.map (fixedModule A L).subtype := by
  rw [augmentation, Subgroup.closure_le]
  rintro _ ⟨g, hg, a, ha, rfl⟩
  have hga := smul_mem_fixedModule_of_normal hLK hg ha
  refine ⟨⟨g • a, hga⟩ / ⟨a, ha⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_div, div_eq_one]
  exact norm_smul ⟨g, hg⟩ ⟨a, ha⟩ hga
end GroundTheory.LocalField.Abstract
