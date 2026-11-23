-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.mk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:21:30.041082+00:00
-- url     : https://prove2.me/submissions/6befb605-efef-42eb-9fb0-b274ab8464c2

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
theorem _root_.solution : Function.Surjective (mk K) := QuotientGroup.mk'_surjective _
end GroundTheory.Global.IdeleClassGroup
