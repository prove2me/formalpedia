-- Prove2me | solution 1 for GlobalTheory.differentiableOn_doublingIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:50.723915+00:00
-- url     : https://prove2.me/submissions/cea83fd1-aec8-493b-a13d-414adb7960f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnDoublingIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem norm_half_smul (z : E) : ‖(2 : ℂ)⁻¹ • z‖ = ‖z‖ / 2 := by
  rw [norm_smul, norm_inv]
  simp [div_eq_inv_mul]
private theorem half_mem_ball {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (2 : ℂ)⁻¹ • z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_half_smul]
  linarith [norm_nonneg z]
private theorem neg_mem_ball' {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    -z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_neg]
end
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory
theorem _root_.solution {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by
  induction n with
  | zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => half_mem_ball hz
    have h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z)))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)
    exact (h1.const_mul 3).add h2
end GlobalTheory
