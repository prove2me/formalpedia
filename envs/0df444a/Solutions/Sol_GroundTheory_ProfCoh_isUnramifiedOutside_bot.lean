-- Prove2me | solution 1 for GroundTheory.ProfCoh.isUnramifiedOutside_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:41:25.943426+00:00
-- url     : https://prove2.me/submissions/0ad08fe0-8b20-4298-9b5e-33f5df4ae68c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Ramification
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_Unramified
import Theorems.Thm_GroundTheory_ProfCoh_isUnramifiedIn_bot

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
theorem _root_.solution (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) :=
  fun v _ => isUnramifiedIn_bot v
end GroundTheory.ProfCoh
