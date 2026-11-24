-- Prove2me | solution 1 for GlobalTheory.LogDerivZeros.norm_logDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:50:15.743708+00:00
-- url     : https://prove2.me/submissions/3ec22d40-7b11-425b-8a16-8330197f93b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LogDerivZeros
namespace GlobalTheory.LogDerivZeros
theorem _root_.solution {r R K : ℝ} (hr : 0 < r) (hrR : r < R) (hK : 0 < K) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (h0 : ∀ z ∈ Metric.ball (0 : ℂ) R, g z ≠ 0)
    (hb : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖g z‖ ≤ ‖g 0‖ * Real.exp K) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖deriv g z / g z‖ ≤ (8 * R / (R - r) ^ 2) * K := by
  have hR : 0 < R := hr.trans hrR
  have hd : DifferentiableOn ℂ (fun u => deriv g u / g u) (Metric.ball 0 R) :=
    (hg.deriv Metric.isOpen_ball).div hg h0
  obtain ⟨h, hh0, hh⟩ := hd.isExactOn_ball.with_val_at 0 0
  have hhd : DifferentiableOn ℂ h (Metric.ball 0 R) :=
    fun u hu => (hh u hu).differentiableAt.differentiableWithinAt
  have hc : ∀ u ∈ Metric.ball (0 : ℂ) R, g u * cexp (-h u) = g 0 := by
    intro u hu
    have hD : ∀ v ∈ Metric.ball (0 : ℂ) R, HasDerivAt (fun v => g v * cexp (-h v)) 0 v := by
      intro v hv
      have h1 := (hg.differentiableAt (Metric.isOpen_ball.mem_nhds hv)).hasDerivAt
      have h2 := h1.mul (hh v hv).neg.cexp
      have := h0 v hv
      refine HasDerivAt.congr_deriv h2 ?_
      simp only [Pi.neg_apply]
      field_simp
      ring
    have := Metric.isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℂ) (f := fun v => g v * cexp (-h v))
      (convex_ball (0 : ℂ) R).isPreconnected
      (fun v hv => (hD v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hD v hv).deriv) hu (Metric.mem_ball_self hR)
    simpa [hh0] using this
  have hre : Set.MapsTo h (Metric.ball 0 R) {z | z.re ≤ K} := by
    intro u hu
    have e : g u = g 0 * cexp (h u) := by
      rw [← hc u hu, mul_assoc, ← Complex.exp_add]; simp
    have h1 := hb u hu
    rw [e, norm_mul, Complex.norm_exp] at h1
    have hp : 0 < ‖g 0‖ := norm_pos_iff.2 (h0 0 (Metric.mem_ball_self hR))
    exact Real.exp_le_exp.1 (le_of_mul_le_mul_left h1 hp)
  have hδ : 0 < (R - r) / 2 := by linarith
  have hsub : Metric.closedBall z ((R - r) / 2) ⊆ Metric.ball 0 R := by
    intro u hu
    rw [mem_closedBall_iff_norm] at hu
    rw [mem_ball_zero_iff]
    have := norm_le_norm_sub_add u z
    linarith
  have hzb : z ∈ Metric.ball (0 : ℂ) R := hsub (Metric.mem_closedBall_self hδ.le)
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (f := h)
    (C := 2 * K * R / ((R - r) / 2)) hδ (hhd.diffContOnCl_ball hsub) (by
      intro u hu
      have hu' := hsub (Metric.sphere_subset_closedBall hu)
      have h1 := Complex.borelCaratheodory_zero hK hhd hre hR hu' hh0
      rw [mem_sphere_iff_norm] at hu
      have h2 := norm_le_norm_sub_add u z
      refine h1.trans ?_
      gcongr
      · exact (mem_ball_zero_iff.1 hu').le
      · linarith)
  rw [(hh z hzb).deriv] at hcau
  refine hcau.trans (le_of_eq ?_)
  have : R - r ≠ 0 := by linarith
  field_simp
  ring
end GlobalTheory.LogDerivZeros
