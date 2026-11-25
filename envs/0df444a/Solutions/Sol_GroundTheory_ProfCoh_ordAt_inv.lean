-- Prove2me | solution 1 for GroundTheory.ProfCoh.ordAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:25:45.060851+00:00
-- url     : https://prove2.me/submissions/48a008a4-a9db-4660-8508-bf690fa82523

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type*} [Field F] [NumberField F]
namespace GroundTheory.ProfCoh
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) : ordAt v x⁻¹ = -ordAt v x := by
  simp [ordAt]
end GroundTheory.ProfCoh
