-- Prove2me | solution 1 for GroundTheory.ProfCoh.charComp_charBar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:51:02.694274+00:00
-- url     : https://prove2.me/submissions/425cced5-03ac-4eb5-8ab9-2d28ab5b2104

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation
import Theorems.Thm_GroundTheory_ProfCoh_charBar_apply

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
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
variable {G : Type} [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charComp (charKer χ) (charBar χ) = χ := by
  ext x
  exact charBar_apply χ (Additive.toMul x)
end GroundTheory.ProfCoh
