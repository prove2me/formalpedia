-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_infiniteModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:10.495917+00:00
-- url     : https://prove2.me/submissions/0ac194f6-c53b-4e7b-b371-8cd24419cb10

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteProj


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
theorem _root_.solution : Continuous (infiniteModule (K := K)) :=
  continuous_finsetProd _ fun w _ ↦
    (continuous_norm.comp (Units.continuous_val.comp (continuous_infiniteProj w))).pow _
end GroundTheory.Global.IdeleGroup
