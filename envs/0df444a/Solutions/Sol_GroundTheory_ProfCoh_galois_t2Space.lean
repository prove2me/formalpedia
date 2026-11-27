-- Prove2me | solution 1 for GroundTheory.ProfCoh.galois_t2Space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:42.412379+00:00
-- url     : https://prove2.me/submissions/45072651-7148-459c-ba92-2442c0de5629

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
theorem _root_.solution [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  inferInstance
end GroundTheory.ProfCoh
