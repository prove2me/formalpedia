-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:19.120811+00:00
-- url     : https://prove2.me/submissions/46840495-d7d8-4837-a064-110e38630178

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
theorem _root_.solution (E : FiniteGaloisIntermediateField K L) :
    ((openNormalSubgroupEquiv.symm (OrderDual.toDual E) : OpenNormalSubgroup Gal(L/K)) :
      Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl
end GroundTheory.ProfCoh
