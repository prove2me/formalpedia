-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_infiniteEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:38.162101+00:00
-- url     : https://prove2.me/submissions/724987da-b820-4e01-aa25-eca6d87aaa9c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteAdeleSingle

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
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) :
    Continuous (infiniteEmbedding (K := K) w) :=
  Units.continuous_map ((continuous_infiniteAdeleSingle w).prodMk continuous_const)
end GroundTheory.Global.IdeleGroup
