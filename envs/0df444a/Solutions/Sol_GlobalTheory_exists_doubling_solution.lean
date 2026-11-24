-- Prove2me | solution 1 for GlobalTheory.exists_doubling_solution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:33:22.264966+00:00
-- url     : https://prove2.me/submissions/82fd9e4d-f3ed-44e4-b20b-247a049d47d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnDoublingIterate
import Theorems.Thm_GlobalTheory_differentiableOn_doublingIterate
import Theorems.Thm_GlobalTheory_norm_doublingIterate_le
import Theorems.Thm_GlobalTheory_SCV_analyticAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_tsum_of_locally_normal

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
theorem _root_.solution [FiniteDimensional ℂ E] (h : E → ℂ) (ha : AnalyticAt ℂ h 0)
    (hO : h =O[𝓝 0] (fun z => ‖z‖ ^ 3)) :
    ∃ k : E → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
      ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z := by
  obtain ⟨C, hC, hO⟩ := hO.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hO.bound.and ha.eventually_analyticAt)
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3 := fun z hz => by
    simpa using (hball z hz).1
  have hB := norm_doublingIterate_le hC hb
  have hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c) :=
    fun c => hasSum_geometric_two.mul_right c
  have hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z :=
    fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz
  refine ⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩
  · refine SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r)
      (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball
        (differentiableOn_doublingIterate hd) fun x hx =>
          ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable,
            fun n z hz => (hB n z hz).trans ?_⟩) (Metric.ball_mem_nhds 0 hr)
    have := (mem_ball_zero_iff.mp hz).le
    gcongr
  · refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    refine (tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_
    simp [mul_assoc]
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz1 : z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      linarith
    have hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z := inv_smul_smul₀ two_ne_zero z
    rw [(hS _ hz2).tsum_eq_zero_add]
    simp only [doublingIterate, e]
    rw [((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]
    ring
end GlobalTheory
