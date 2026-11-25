-- Prove2me | solution 1 for GroundTheory.ProfCoh.galois_isProfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:50.920793+00:00
-- url     : https://prove2.me/submissions/985c3449-df18-4b63-893d-e940f54c5460

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open IntermediateField
universe w u
variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]
variable (K L)
namespace GroundTheory.ProfCoh
theorem _root_.solution [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩
end GroundTheory.ProfCoh
