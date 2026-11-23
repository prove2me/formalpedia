-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.top_mem_rectBoundary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:10.695906+00:00
-- url     : https://prove2.me/submissions/8842c8fd-9b27-41ee-979f-4735ef121d57

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
theorem _root_.solution {x : ℝ} (hx : x ∈ [[z.re, w.re]]) :
    (x : ℂ) + w.im * I ∈ rectBoundary z w := by
  simp [rectBoundary, mem_reProdIm, hx]
end GroundTheory.Global.Elliptic
