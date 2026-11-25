-- Prove2me | solution 1 for GroundTheory.Global.continuous_ideleNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:34.057252+00:00
-- url     : https://prove2.me/submissions/c344d4f2-6279-4b41-829a-16fb09cb6f79

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_norm_adeleRing

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
theorem _root_.solution : Continuous (ideleNorm K L) :=
  Continuous.units_map _ continuous_norm_adeleRing
end GroundTheory.Global
