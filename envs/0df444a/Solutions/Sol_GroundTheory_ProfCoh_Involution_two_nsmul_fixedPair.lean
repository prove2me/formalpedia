-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.two_nsmul_fixedPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:41.768468+00:00
-- url     : https://prove2.me/submissions/c50aad8f-1f3c-4241-8a05-77cc9b50b890

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_RealPlaces_InvolutionDuality

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
open GroundTheory.ProfCoh.Involution
variable {M : Type*} [AddCommGroup M]
namespace GroundTheory.ProfCoh.Involution
theorem _root_.solution (σ : M →+ M) (x : fixedSub σ) (f : fixedSub (dualInv σ)) :
    2 • fixedPair σ x f = 0 := by
  rw [fixedPair_apply, two_nsmul]
  have hx : σ x = x := mem_fixedSub.1 x.2
  have hf := (mem_fixedSub_dualInv_iff (f : M →+ QZ)).1 f.2 x
  rwa [hx, map_add] at hf
end GroundTheory.ProfCoh.Involution
