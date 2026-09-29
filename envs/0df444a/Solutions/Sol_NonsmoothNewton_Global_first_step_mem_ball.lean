-- Prove2me | solution 1 for NonsmoothNewton.Global.first_step_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:50:45.656033+00:00
-- url     : https://prove2.me/submissions/686b624a-b0c2-4ab2-a301-b734c5850d8e

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r β γ δ : ℝ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n), V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (V0 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x1 : EuclideanSpace ℝ (Fin n))
    (hV0 : V0 ∈ clarkeJac F x0) (hstep : V0 (x1 - x0) = -F x0) :
    ‖x1 - x0‖ ≤ β * ‖F x0‖ ∧ ‖x1 - x0‖ ≤ r * (1 - β * (γ + δ)) ∧ x1 ∈ Metric.closedBall x0 r := by
  have hx0 : x0 ∈ Metric.closedBall x0 r := Metric.mem_closedBall_self hr0
  obtain ⟨W, _hVW, hWV, hWβ⟩ := hinv x0 hx0 V0 hV0
  have hd : x1 - x0 = W (-F x0) := by
    rw [← hstep]
    have := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => L (x1 - x0)) hWV
    simpa using this.symm
  have h1 : ‖x1 - x0‖ ≤ β * ‖F x0‖ := by
    rw [hd]
    calc ‖W (-F x0)‖ ≤ ‖W‖ * ‖-F x0‖ := W.le_opNorm _
      _ ≤ β * ‖F x0‖ := by
        rw [norm_neg]; exact mul_le_mul_of_nonneg_right hWβ (norm_nonneg _)
  have h2 : ‖x1 - x0‖ ≤ r * (1 - β * (γ + δ)) := h1.trans hr
  refine ⟨h1, h2, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · subst h0; simpa using h2
  by_cases hdz : x1 - x0 = 0
  · rw [hdz, norm_zero]; exact hr0
  have hdn : 0 < ‖x1 - x0‖ := norm_pos_iff.mpr hdz
  have hyx : ‖(x0 + (r / ‖x1 - x0‖) • (x1 - x0)) - x0‖ = r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hpos hdn),
      div_mul_cancel₀ _ hdn.ne']
  have hy : x0 + (r / ‖x1 - x0‖) • (x1 - x0) ∈ Metric.closedBall x0 r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hyx]
  have hγ0 : 0 ≤ γ := by
    have := hγ x0 hx0 _ hy V0 hV0
    rw [hyx] at this
    have h' : 0 ≤ γ * r := (norm_nonneg _).trans this
    exact nonneg_of_mul_nonneg_left h' hpos
  have hδ0 : 0 ≤ δ := by
    have := hδ x0 hx0 _ hy
    rw [hyx] at this
    have h' : 0 ≤ δ * r := (norm_nonneg _).trans this
    exact nonneg_of_mul_nonneg_left h' hpos
  have hβ0 : 0 ≤ β := (norm_nonneg W).trans hWβ
  have hα0 : 0 ≤ β * (γ + δ) := mul_nonneg hβ0 (add_nonneg hγ0 hδ0)
  nlinarith
