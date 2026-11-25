-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_infiniteAdeleSingle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:07:04.368022+00:00
-- url     : https://prove2.me/submissions/55cd7c74-fdeb-4e81-b430-aa2ae33d733a

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
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (w : InfinitePlace K) :
    Continuous (infiniteAdeleSingle w) := by
  classical
  exact continuous_mulSingle (A := fun u : InfinitePlace K ↦ u.Completion) w
end GroundTheory.Global.IdeleGroup
