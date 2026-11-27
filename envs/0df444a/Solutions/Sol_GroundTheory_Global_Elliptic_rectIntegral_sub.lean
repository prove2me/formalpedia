-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:18.52387+00:00
-- url     : https://prove2.me/submissions/b6d26556-63f5-4879-b335-940dd455564e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_bottom
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_top
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_right
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_left

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
theorem _root_.solution (hf : ContinuousOn f (rectBoundary z w))
    (hg : ContinuousOn g (rectBoundary z w)) :
    rectIntegral (fun u ↦ f u - g u) z w = rectIntegral f z w - rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_sub (intervalIntegrable_bottom hf) (intervalIntegrable_bottom hg),
    integral_sub (intervalIntegrable_top hf) (intervalIntegrable_top hg),
    integral_sub (intervalIntegrable_right hf) (intervalIntegrable_right hg),
    integral_sub (intervalIntegrable_left hf) (intervalIntegrable_left hg)]
  simp only [smul_sub]
  abel
end GroundTheory.Global.Elliptic
