-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectBoundary_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:18.934831+00:00
-- url     : https://prove2.me/submissions/e62a33ab-f591-4d7f-b8e8-a06b5cedaefe

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
theorem _root_.solution : rectBoundary z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  intro u hu
  simp only [rectBoundary, mem_union, mem_reProdIm, mem_singleton_iff] at hu ⊢
  rcases hu with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
  · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
  · exact ⟨h1 ▸ left_mem_uIcc, h2⟩
  · exact ⟨h1 ▸ right_mem_uIcc, h2⟩
end GroundTheory.Global.Elliptic
