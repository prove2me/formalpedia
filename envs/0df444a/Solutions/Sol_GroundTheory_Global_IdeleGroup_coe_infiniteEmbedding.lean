-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:29.653744+00:00
-- url     : https://prove2.me/submissions/ba5506d1-eefb-4795-8d17-935638ea0dd6

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
theorem _root_.solution (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((infiniteEmbedding w x : IdeleGroup K) : 𝔸[K]) =
      (infiniteAdeleSingle w (x : w.Completion), 1) :=
  rfl
end GroundTheory.Global.IdeleGroup
