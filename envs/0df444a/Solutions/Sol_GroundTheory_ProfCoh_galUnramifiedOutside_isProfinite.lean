-- Prove2me | solution 1 for GroundTheory.ProfCoh.galUnramifiedOutside_isProfinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:07:04.958808+00:00
-- url     : https://prove2.me/submissions/31db071b-5d32-4311-b3f2-77c4ab987d24

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Theorems.Thm_GroundTheory_ProfCoh_galois_isProfinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))
variable [NumberField F] [IsGalois F Ω]
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    CompactSpace (galUnramifiedOutside F Ω S) ∧ T2Space (galUnramifiedOutside F Ω S) ∧
      TotallyDisconnectedSpace (galUnramifiedOutside F Ω S) :=
  galois_isProfinite F (maxUnramifiedOutside F Ω S)
end GroundTheory.ProfCoh
