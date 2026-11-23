-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.isOpenMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:30.478525+00:00
-- url     : https://prove2.me/submissions/45a3ce0d-1137-4f22-9f29-86b763c52d3c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe

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
open GroundTheory.Global.IdeleClassGroup
namespace GroundTheory.Global.IdeleClassGroup
theorem _root_.solution : IsOpenMap (mk K) := QuotientGroup.isOpenMap_coe
end GroundTheory.Global.IdeleClassGroup
