-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:57.507885+00:00
-- url     : https://prove2.me/submissions/52e0e658-cc46-44c4-a16b-72e8429b340f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
universe w u v
variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) :=
  rfl
end GroundTheory.ProfCoh
