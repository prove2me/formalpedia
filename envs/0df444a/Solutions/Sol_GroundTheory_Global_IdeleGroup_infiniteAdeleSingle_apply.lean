-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:04.645953+00:00
-- url     : https://prove2.me/submissions/5f1d52b0-4e14-43aa-afd3-8d2e71b62af4

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
omit [NumberField K]
open Classical
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w u : InfinitePlace K) (x : w.Completion) :
    infiniteAdeleSingle w x u = Pi.mulSingle (M := fun u : InfinitePlace K ↦ u.Completion) w x u :=
  rfl
end GroundTheory.Global.IdeleGroup
