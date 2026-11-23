-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:01.597696+00:00
-- url     : https://prove2.me/submissions/6fc6bac6-b79b-4224-a823-0ba8df8033fa

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
open Classical
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (v w : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x w = Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) ↦
      u.adicCompletion K) v x w := rfl
end GroundTheory.Global.IdeleGroup
