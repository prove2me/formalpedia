-- Prove2me | solution 2 for GroundTheory.Global.Elliptic.rectIntegral_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:15.821907+00:00
-- url     : https://prove2.me/submissions/4e39e3dc-b4cc-4a72-85a1-b539231792d1

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
theorem _root_.solution : rectIntegral (fun u ↦ -f u) z w = -rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_neg, smul_neg]
  abel
end GroundTheory.Global.Elliptic
