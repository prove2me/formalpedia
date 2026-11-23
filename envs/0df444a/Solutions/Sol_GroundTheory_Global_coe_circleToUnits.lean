-- Prove2me | solution 1 for GroundTheory.Global.coe_circleToUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:06.076602+00:00
-- url     : https://prove2.me/submissions/341ee272-56c2-403d-9d7c-607beb99e8ce

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex
namespace GroundTheory.Global
theorem _root_.solution (z : Circle) : ((circleToUnits z : ℂˣ) : ℂ) = z := rfl
end GroundTheory.Global
