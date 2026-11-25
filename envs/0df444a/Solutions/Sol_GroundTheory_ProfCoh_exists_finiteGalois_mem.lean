-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_finiteGalois_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:46.422791+00:00
-- url     : https://prove2.me/submissions/b6ba843a-96af-4ed0-abcb-89cf3dd5edef

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
theorem _root_.solution (x : L) :
    ∃ F : FiniteGaloisIntermediateField K L, x ∈ F.toIntermediateField :=
  ⟨FiniteGaloisIntermediateField.adjoin K {x},
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩
end GroundTheory.ProfCoh
