-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.right_mem_rectBoundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:09.827239+00:00
-- url     : https://prove2.me/submissions/74c780ee-ea3a-4be3-bd60-e62493a08365

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
variable {z w : ℂ}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {y : ℝ} (hy : y ∈ [[z.im, w.im]]) :
    (w.re : ℂ) + y * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hy]
end GroundTheory.Global.Elliptic
