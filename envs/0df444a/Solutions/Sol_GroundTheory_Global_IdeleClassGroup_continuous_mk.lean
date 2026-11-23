-- Prove2me | solution 1 for GroundTheory.Global.IdeleClassGroup.continuous_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:50.991813+00:00
-- url     : https://prove2.me/submissions/176287d1-78ec-493a-88b7-bd95c1aa45e0

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
theorem _root_.solution : Continuous (mk K) := QuotientGroup.continuous_mk
end GroundTheory.Global.IdeleClassGroup
