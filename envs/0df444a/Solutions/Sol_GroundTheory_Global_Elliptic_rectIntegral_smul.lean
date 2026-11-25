-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:22.570643+00:00
-- url     : https://prove2.me/submissions/0ec5a2cc-9c20-4a0d-8fe2-8fe42feca83c

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
theorem _root_.solution (c : ℂ) : rectIntegral (fun u ↦ c • f u) z w = c • rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_smul, smul_sub, smul_add]
  rw [smul_comm I c, smul_comm I c]
end GroundTheory.Global.Elliptic
