-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:04.356066+00:00
-- url     : https://prove2.me/submissions/2fd92dd7-0bc5-4ffe-8ca2-7222c53add72

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ} {f g : ℂ → E}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution : rectIntegral (fun _ ↦ (0 : E)) z w = 0 := by
  simp [rectIntegral]
end GroundTheory.Global.Elliptic
