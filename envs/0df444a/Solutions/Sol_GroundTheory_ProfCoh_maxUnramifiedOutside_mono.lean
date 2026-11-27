-- Prove2me | solution 1 for GroundTheory.ProfCoh.maxUnramifiedOutside_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:23.694799+00:00
-- url     : https://prove2.me/submissions/43cc9314-a7e9-40bb-b0f4-24b319558616

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside

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
namespace GroundTheory.ProfCoh
theorem _root_.solution {S T : Set (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    maxUnramifiedOutside F Ω S ≤ maxUnramifiedOutside F Ω T :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_le fun hE =>
    le_iSup_of_le (fun v hv => hE v fun hs => hv (h hs)) le_rfl
end GroundTheory.ProfCoh
