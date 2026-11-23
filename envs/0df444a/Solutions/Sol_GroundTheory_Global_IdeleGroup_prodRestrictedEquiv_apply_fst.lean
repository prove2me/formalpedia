-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:22.721932+00:00
-- url     : https://prove2.me/submissions/47a6050d-8595-450b-82a5-76f9bdf2a31d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted

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
open Filter Topology NumberField IsDedekindDomain
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : IdeleGroup K) :
    ((prodRestrictedEquiv K x).1 : InfiniteAdeleRing K) = (x : 𝔸[K]).1 :=
  rfl
end GroundTheory.Global.IdeleGroup
