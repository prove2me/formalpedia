-- Prove2me | solution 1 for GlobalTheory.norm_doublingIterate_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:26:59.476676+00:00
-- url     : https://prove2.me/submissions/cdcd53a1-cebd-4077-a44f-77a6025eca75

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
theorem _root_.solution {h : E → ℂ} {r C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3) (n : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖doublingIterate h n z‖ ≤ (1 / 2) ^ n * (C * ‖z‖ ^ 3) := by
  induction n with
  | zero =>
    intro z hz
    have h1 := hh _ (half_mem_ball hz)
    rw [norm_half_smul] at h1
    have h2 : 0 ≤ C * ‖z‖ ^ 3 := by positivity
    change ‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _
    nlinarith
  | succ n ih =>
    intro z hz
    have h1 := ih _ (half_mem_ball hz)
    have h2 := ih _ (neg_mem_ball' (half_mem_ball hz))
    rw [norm_neg] at h2
    rw [norm_half_smul] at h1 h2
    change ‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z)
      + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3]
    calc _ ≤ 3 * ((1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3)) + (1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3) := by
          gcongr
      _ = _ := by ring
end GlobalTheory
