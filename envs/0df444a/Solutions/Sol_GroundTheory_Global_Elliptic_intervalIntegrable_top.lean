-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.intervalIntegrable_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:48.100393+00:00
-- url     : https://prove2.me/submissions/3458e3ae-c4db-4158-808c-65a48b17a35e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_top_mem_rectBoundary

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
    IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * I)) volume z.re w.re :=
  (hf.comp (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + w.im * I).continuousOn
    fun _ hx ↦ top_mem_rectBoundary hx).intervalIntegrable
end GroundTheory.Global.Elliptic
