-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_neg
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:37:30.888848+00:00
-- url     : https://prove2.me/submissions/37212114-4d0b-4687-9f9f-642d7b29784c

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
theorem _root_.solution : rectIntegral (fun u ↦ -f u) z w = -rectIntegral f z w := by
  first
    | (unfold GroundTheory.Global.Elliptic.rectIntegral
       simp only [Pi.neg_apply, intervalIntegral.integral_neg, smul_neg]
       abel)
    | (unfold GroundTheory.Global.Elliptic.rectIntegral
       simp
       ring)

