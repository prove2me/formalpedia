-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_finiteGalois_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:11.40285+00:00
-- url     : https://prove2.me/submissions/d89cba07-935e-411a-a691-f45814bb7118

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
theorem _root_.solution (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ F : FiniteGaloisIntermediateField K L, E ≤ F.toIntermediateField :=
  ⟨{ toIntermediateField := normalClosure K E L
     finiteDimensional := normalClosure.is_finiteDimensional K E L
     isGalois := IsGalois.normalClosure K E L }, le_normalClosure E⟩
end GroundTheory.ProfCoh
