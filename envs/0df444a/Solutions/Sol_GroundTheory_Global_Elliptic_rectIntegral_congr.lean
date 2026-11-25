-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:19.761678+00:00
-- url     : https://prove2.me/submissions/29583e31-424b-4fde-b6d7-1f5ee861cc0b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_bottom_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_top_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_right_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_left_mem_rectBoundary

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
theorem _root_.solution (h : EqOn f g (rectBoundary z w)) :
    rectIntegral f z w = rectIntegral g z w := by
  simp only [rectIntegral]
  rw [integral_congr (g := fun x : ℝ ↦ g (x + z.im * I))
      fun x hx ↦ h (bottom_mem_rectBoundary hx),
    integral_congr (g := fun x : ℝ ↦ g (x + w.im * I)) fun x hx ↦ h (top_mem_rectBoundary hx),
    integral_congr (g := fun y : ℝ ↦ g (w.re + y * I)) fun y hy ↦ h (right_mem_rectBoundary hy),
    integral_congr (g := fun y : ℝ ↦ g (z.re + y * I)) fun y hy ↦ h (left_mem_rectBoundary hy)]
end GroundTheory.Global.Elliptic
