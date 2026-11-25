-- Prove2me | solution 1 for GroundTheory.Global.isCoveringMap_circleExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:49.104806+00:00
-- url     : https://prove2.me/submissions/30d3c076-e045-4c0a-8af8-d72144d83db6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchChars

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
theorem _root_.solution : IsCoveringMap (Circle.exp : ℝ → Circle) := by
  have h : IsCoveringMap ((↑) : ℝ → AddCircle (2 * Real.pi)) := AddCircle.isCoveringMap_coe _
  exact h.homeomorph_comp AddCircle.homeomorphCircle'
end GroundTheory.Global
