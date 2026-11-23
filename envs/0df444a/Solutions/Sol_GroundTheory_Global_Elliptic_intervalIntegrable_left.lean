-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.intervalIntegrable_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:47.911499+00:00
-- url     : https://prove2.me/submissions/81dad62c-5528-4c6f-a668-60130a1c5ea7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
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
variable {z w : ℂ}
variable {f g : ℂ → E}
omit [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (hf : ContinuousOn f (rectBoundary z w)) :
    IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * I)) volume z.im w.im :=
  (hf.comp (by fun_prop : Continuous fun y : ℝ ↦ (z.re : ℂ) + y * I).continuousOn
    fun _ hy ↦ left_mem_rectBoundary hy).intervalIntegrable
end GroundTheory.Global.Elliptic
