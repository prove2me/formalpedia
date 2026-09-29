-- Prove2me | solution 1 for NonsmoothNewton.Global.newton_step_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:50:54.115074+00:00
-- url     : https://prove2.me/submissions/e1b6cac9-8a8b-407a-965f-759186afc3d6

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

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
    (xkm1 xk xkp1 : EuclideanSpace ℝ (Fin n)) (Vkm1 Vk : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hxkm1 : xkm1 ∈ Metric.closedBall x0 r) (hxk : xk ∈ Metric.closedBall x0 r)
    (hVkm1 : Vkm1 ∈ clarkeJac F xkm1) (hstepkm1 : Vkm1 (xk - xkm1) = -F xkm1)
    (hVk : Vk ∈ clarkeJac F xk) (hstepk : Vk (xkp1 - xk) = -F xk) :
    ‖xkp1 - xk‖ ≤ β * ‖F xk‖ ∧
      ‖xkp1 - xk‖ ≤ β * (δ + γ) * ‖xk - xkm1‖ := by
  obtain ⟨W, _hVW, hWV, hWβ⟩ := hinv xk hxk Vk hVk
  have hβ : 0 ≤ β := le_trans (norm_nonneg _) hWβ
  have hstep : xkp1 - xk = W (-F xk) := by
    have h1 : (W.comp Vk) (xkp1 - xk) = xkp1 - xk := by
      rw [hWV]; rfl
    rw [← h1, ContinuousLinearMap.comp_apply, hstepk]
  have hfirst : ‖xkp1 - xk‖ ≤ β * ‖F xk‖ := by
    rw [hstep]
    calc ‖W (-F xk)‖ ≤ ‖W‖ * ‖-F xk‖ := W.le_opNorm _
      _ = ‖W‖ * ‖F xk‖ := by rw [norm_neg]
      _ ≤ β * ‖F xk‖ := mul_le_mul_of_nonneg_right hWβ (norm_nonneg _)
  have hFxk : ‖F xk‖ ≤ (δ + γ) * ‖xk - xkm1‖ := by
    have hd := hδ xkm1 hxkm1 xk hxk
    have hg := hγ xkm1 hxkm1 xk hxk Vkm1 hVkm1
    rw [hstepkm1] at hg
    have heq : F xk = (F xk - F xkm1 - dirDeriv F xkm1 (xk - xkm1))
        - (-F xkm1 - dirDeriv F xkm1 (xk - xkm1)) := by abel
    rw [heq]
    calc _ ≤ ‖F xk - F xkm1 - dirDeriv F xkm1 (xk - xkm1)‖
          + ‖-F xkm1 - dirDeriv F xkm1 (xk - xkm1)‖ := norm_sub_le _ _
      _ ≤ δ * ‖xk - xkm1‖ + γ * ‖xk - xkm1‖ := add_le_add hd hg
      _ = (δ + γ) * ‖xk - xkm1‖ := by ring
  refine ⟨hfirst, ?_⟩
  calc ‖xkp1 - xk‖ ≤ β * ‖F xk‖ := hfirst
    _ ≤ β * ((δ + γ) * ‖xk - xkm1‖) := mul_le_mul_of_nonneg_left hFxk hβ
    _ = β * (δ + γ) * ‖xk - xkm1‖ := by ring
