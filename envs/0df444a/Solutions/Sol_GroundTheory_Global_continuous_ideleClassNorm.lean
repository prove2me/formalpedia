-- Prove2me | solution 1 for GroundTheory.Global.continuous_ideleClassNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:59.630666+00:00
-- url     : https://prove2.me/submissions/fbc84fb9-bb85-401d-9cd1-76531341786d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_continuous_ideleNorm
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_continuous_mk


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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
namespace GroundTheory.Global
theorem _root_.solution : Continuous (ideleClassNorm K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    ((IdeleClassGroup.continuous_mk K).comp continuous_ideleNorm)
end GroundTheory.Global
