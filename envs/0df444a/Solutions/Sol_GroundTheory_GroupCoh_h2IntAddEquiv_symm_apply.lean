-- Prove2me | solution 1 for GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:26.030559+00:00
-- url     : https://prove2.me/submissions/fce93a96-afff-4518-960c-4eeedce68725

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_Characters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
variable (G : Type) [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h2IntAddEquiv G).symm χ =
      groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ) :=
  rfl
end GroundTheory.GroupCoh
