-- Prove2me | solution 1 for GroundTheory.GroupCoh.triangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:34:38.278904+00:00
-- url     : https://prove2.me/submissions/1fdfcd1e-a8af-4706-a443-a618429a791a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
namespace GroundTheory.GroupCoh
theorem _root_.solution : triangle 0 = 0 := rfl
end GroundTheory.GroupCoh
