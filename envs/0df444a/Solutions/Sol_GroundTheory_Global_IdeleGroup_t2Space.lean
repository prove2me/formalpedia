-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.t2Space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:35:41.991807+00:00
-- url     : https://prove2.me/submissions/3a44542d-789c-44d5-9491-b09c03238a7c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Global
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
namespace IdeleGroup
theorem _root_.solution : T2Space (IdeleGroup K) :=
  inferInstance
end IdeleGroup
end GroundTheory.Global
