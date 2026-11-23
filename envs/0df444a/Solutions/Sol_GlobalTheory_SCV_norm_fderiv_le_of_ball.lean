-- Prove2me | solution 1 for GlobalTheory.SCV.norm_fderiv_le_of_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:06.87096+00:00
-- url     : https://prove2.me/submissions/0cc93258-617b-4f4f-b4d9-34d8202af94f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {c : E} {r M : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f c‖ ≤ 2 * M / r := by
  refine Complex.norm_fderiv_le_div_of_mapsTo_ball hf (fun z hz => ?_) hr
  rw [mem_closedBall_iff_norm]
  have := norm_sub_le (f z) (f c)
  linarith [hM z hz, hM c (mem_ball_self hr)]
end GlobalTheory.SCV
