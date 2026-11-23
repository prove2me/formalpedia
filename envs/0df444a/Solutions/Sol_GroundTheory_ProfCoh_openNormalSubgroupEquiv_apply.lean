-- Prove2me | solution 1 for GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:40.268849+00:00
-- url     : https://prove2.me/submissions/a960cd43-dc40-4734-b19f-db3b4d8cb028

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField InfiniteGalois
universe u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable [IsGalois K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (U : OpenNormalSubgroup Gal(L/K)) :
    (OrderDual.ofDual (openNormalSubgroupEquiv U)).toIntermediateField =
      fixedField (U : Subgroup Gal(L/K)) :=
  rfl
end GroundTheory.ProfCoh
