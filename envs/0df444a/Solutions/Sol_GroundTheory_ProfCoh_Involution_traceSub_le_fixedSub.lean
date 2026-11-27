-- Prove2me | solution 1 for GroundTheory.ProfCoh.Involution.traceSub_le_fixedSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:36.142496+00:00
-- url     : https://prove2.me/submissions/ae141c6a-c449-46b5-9b76-3ead49cdd586

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
theorem _root_.solution {σ : M →+ M} (hσ : ∀ x, σ (σ x) = x) : traceSub σ ≤ fixedSub σ := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_traceSub.1 hx
  rw [mem_fixedSub, map_add, hσ, add_comm]
end GroundTheory.ProfCoh.Involution
