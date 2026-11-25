-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_ideleModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:57.930863+00:00
-- url     : https://prove2.me/submissions/26149809-5cb6-43e2-885c-421c432f8fe9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteModule
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_finiteModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution : Continuous (ideleModule K) :=
  (continuous_infiniteModule.mul continuous_finiteModule).subtype_mk _
end GroundTheory.Global.IdeleGroup
