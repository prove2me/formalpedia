-- Prove2me | solution 1 for GroundTheory.ProfCoh.galois_compactSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:38.923115+00:00
-- url     : https://prove2.me/submissions/8ab97e3a-b062-48e3-8c8d-806f2662f589

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
theorem _root_.solution [IsGalois K L] : CompactSpace Gal(L/K) :=
  inferInstance
end GroundTheory.ProfCoh
