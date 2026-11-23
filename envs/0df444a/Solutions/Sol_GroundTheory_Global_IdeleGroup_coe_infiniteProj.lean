-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_infiniteProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:29.824147+00:00
-- url     : https://prove2.me/submissions/6ea3d9ca-1238-42d3-b2d0-15adb397d61c

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
open GroundTheory.Global.IdeleGroup
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) (x : IdeleGroup K) :
    ((infiniteProj w x : (w.Completion)ˣ) : w.Completion) = (x : 𝔸[K]).1 w :=
  rfl
end GroundTheory.Global.IdeleGroup
