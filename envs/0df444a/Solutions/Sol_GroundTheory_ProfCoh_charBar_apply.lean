-- Prove2me | solution 1 for GroundTheory.ProfCoh.charBar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:25.412202+00:00
-- url     : https://prove2.me/submissions/917ebb10-44e5-42ee-a38b-3af1b1ca572f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation

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
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charBar χ (Additive.ofMul (x : G ⧸ charKer χ)) = χ (Additive.ofMul x) :=
  rfl
end GroundTheory.ProfCoh
