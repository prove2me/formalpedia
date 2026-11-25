-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsUnramifiedOutside.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:39:29.630751+00:00
-- url     : https://prove2.me/submissions/1bf78e0b-4706-4874-adf7-1b6c626cbcba

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain
open scoped Pointwise
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
variable [IsGalois F Ω]
namespace GroundTheory.ProfCoh
namespace IsUnramifiedOutside
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 F))} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : IsUnramifiedOutside S E) (τ : Gal(Ω/F)) :
    IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω)) :=
  fun v hv => isUnramifiedIn_map v (hE v hv) τ
end IsUnramifiedOutside
end GroundTheory.ProfCoh
