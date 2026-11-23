-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.intervalIntegrable_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:48.080315+00:00
-- url     : https://prove2.me/submissions/0ba48e45-0de5-46bd-8097-906503cb0da1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_right_mem_rectBoundary

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
variable {z w : ℂ}
variable {f g : ℂ → E}
omit [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (w.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ right_mem_rectBoundary hy).intervalIntegrable
end GroundTheory.Global.Elliptic
