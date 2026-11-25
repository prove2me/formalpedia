-- Prove2me | solution 1 for GroundTheory.GroupCoh.augCocycle_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:23:30.542717+00:00
-- url     : https://prove2.me/submissions/5772365c-b2a9-4437-baad-cd8780226522

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable (k G : Type u) [CommRing k] [Group G]
variable {k G}
variable (k) {H : Type u} [Group H] (φ : H →* G)
namespace GroundTheory.GroupCoh
theorem _root_.solution (h : H) : augCocycle k φ h = augIdealSubOne (φ h) := rfl
end GroundTheory.GroupCoh
