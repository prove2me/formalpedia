-- Prove2me | solution 2 for GroundTheory.ProfCoh.mem_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:13.890165+00:00
-- url     : https://prove2.me/submissions/09d52e8c-00d4-4bb3-8001-fa5d61420e9c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_MaxUnramifiedOutside

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
variable {F : Type*} [Field F]
variable {L : Type*} [Field L] [Algebra F L]
namespace GroundTheory.ProfCoh
theorem _root_.solution {S : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal :=
  Iff.rfl
end GroundTheory.ProfCoh
