-- Prove2me | solution 1 for GlobalTheory.SCV.exists_ball_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:41.366843+00:00
-- url     : https://prove2.me/submissions/16af2d13-c0fc-4afa-9119-93be7af2e952

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
theorem _root_.solution {f : E → V} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {c : E} (hc : c ∈ U) : ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ z ∈ ball c r, ‖f z‖ ≤ M := by
  have h1 : ContinuousAt f c := (hf.differentiableAt (hU.mem_nhds hc)).continuousAt
  have h2 : ∀ᶠ z in 𝓝 c, z ∈ U ∧ ‖f z‖ < ‖f c‖ + 1 :=
    (Filter.Eventually.and (hU.mem_nhds hc) (h1.norm.eventually (gt_mem_nhds (lt_add_one _))))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp h2
  exact ⟨r, hr, ‖f c‖ + 1, fun z hz => (h z hz).1, fun z hz => (h z hz).2.le⟩
end GlobalTheory.SCV
