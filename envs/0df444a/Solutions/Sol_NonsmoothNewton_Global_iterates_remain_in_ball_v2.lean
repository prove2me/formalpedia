-- Prove2me | solution 1 for NonsmoothNewton.Global.iterates_remain_in_ball_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:22:14.652088+00:00
-- url     : https://prove2.me/submissions/3d29bffb-391b-4c1f-b17f-27d6c4a55fe4

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

set_option autoImplicit false

open NonsmoothNewton.Global Filter Topology in
theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n))
    (r β γ δ : ℝ)
    (hβ0 : 0 ≤ β) (hγ0 : 0 ≤ γ) (hδ0 : 0 ≤ δ)
    (hF : LocallyLipschitz F)
    (hsemi : ∀ x ∈ Metric.closedBall x0 r, SemismoothAt F x)
    (hinv : ∀ x ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ∃ W : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        V.comp W = 1 ∧ W.comp V = 1 ∧ ‖W‖ ≤ β)
    (hγ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r, ∀ V ∈ clarkeJac F x,
      ‖V (y - x) - dirDeriv F x (y - x)‖ ≤ γ * ‖y - x‖)
    (hδ : ∀ x ∈ Metric.closedBall x0 r, ∀ y ∈ Metric.closedBall x0 r,
      ‖F y - F x - dirDeriv F x (y - x)‖ ≤ δ * ‖y - x‖)
    (hα : β * (γ + δ) < 1)
    (hr0 : 0 ≤ r) (hr : β * ‖F x0‖ ≤ r * (1 - β * (γ + δ)))
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hx0 : x 0 = x0) (hrun : IsNewtonRun F x V) :
    ∀ k, x k ∈ Metric.closedBall x0 r ∧
      ‖x (k + 1) - x k‖ ≤ r * (β * (γ + δ)) ^ k * (1 - β * (γ + δ)) := by
  set α := β * (γ + δ) with hαdef
  have hα0 : 0 ≤ α := mul_nonneg hβ0 (add_nonneg hγ0 hδ0)
  -- step bound: ‖d_k‖ ≤ β ‖F x_k‖ when x_k ∈ S
  have stepA : ∀ k, x k ∈ Metric.closedBall x0 r →
      ‖x (k + 1) - x k‖ ≤ β * ‖F (x k)‖ := by
    intro k hk
    obtain ⟨hVk, hNk⟩ := hrun k
    obtain ⟨W, -, hWV, hW⟩ := hinv (x k) hk (V k) hVk
    have hd : x (k + 1) - x k = W (-F (x k)) := by
      rw [← hNk]
      have := congrArg (fun T => T (x (k + 1) - x k)) hWV
      simpa using this.symm
    rw [hd]
    calc ‖W (-F (x k))‖ ≤ ‖W‖ * ‖-F (x k)‖ := W.le_opNorm _
      _ = ‖W‖ * ‖F (x k)‖ := by rw [norm_neg]
      _ ≤ β * ‖F (x k)‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg _)
  -- F bound: ‖F x_{k+1}‖ ≤ (γ+δ) ‖d_k‖ when x_k, x_{k+1} ∈ S
  have stepB : ∀ k, x k ∈ Metric.closedBall x0 r → x (k + 1) ∈ Metric.closedBall x0 r →
      ‖F (x (k + 1))‖ ≤ (γ + δ) * ‖x (k + 1) - x k‖ := by
    intro k hk hk1
    obtain ⟨hVk, hNk⟩ := hrun k
    have h1 := hδ (x k) hk (x (k + 1)) hk1
    have h2 := hγ (x k) hk (x (k + 1)) hk1 (V k) hVk
    have heq : F (x (k + 1)) =
        (F (x (k + 1)) - F (x k) - dirDeriv F (x k) (x (k + 1) - x k)) -
          (V k (x (k + 1) - x k) - dirDeriv F (x k) (x (k + 1) - x k)) := by
      rw [hNk]; abel
    rw [heq]
    calc _ ≤ ‖F (x (k + 1)) - F (x k) - dirDeriv F (x k) (x (k + 1) - x k)‖ +
          ‖V k (x (k + 1) - x k) - dirDeriv F (x k) (x (k + 1) - x k)‖ := norm_sub_le _ _
      _ ≤ δ * ‖x (k + 1) - x k‖ + γ * ‖x (k + 1) - x k‖ := add_le_add h1 h2
      _ = (γ + δ) * ‖x (k + 1) - x k‖ := by ring
  have hmem : ∀ k, ‖x k - x0‖ ≤ r * (1 - α ^ k) → x k ∈ Metric.closedBall x0 r := by
    intro k hk
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : 0 ≤ α ^ k := pow_nonneg hα0 k
    nlinarith
  have main : ∀ k, ‖x k - x0‖ ≤ r * (1 - α ^ k) ∧
      ‖x (k + 1) - x k‖ ≤ r * α ^ k * (1 - α) := by
    intro k
    induction k with
    | zero =>
      have hx0m : x 0 ∈ Metric.closedBall x0 r := by
        rw [hx0]; exact Metric.mem_closedBall_self hr0
      refine ⟨by simp [hx0], ?_⟩
      have := stepA 0 hx0m
      rw [hx0] at this ⊢
      simpa using this.trans hr
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hk := hmem k ih1
      have h1 : ‖x (k + 1) - x0‖ ≤ r * (1 - α ^ (k + 1)) := by
        have : x (k + 1) - x0 = (x (k + 1) - x k) + (x k - x0) := by abel
        rw [this]
        calc _ ≤ ‖x (k + 1) - x k‖ + ‖x k - x0‖ := norm_add_le _ _
          _ ≤ r * α ^ k * (1 - α) + r * (1 - α ^ k) := add_le_add ih2 ih1
          _ = r * (1 - α ^ (k + 1)) := by ring
      refine ⟨h1, ?_⟩
      have hk1 := hmem (k + 1) h1
      have hA := stepA (k + 1) hk1
      have hB := stepB k hk hk1
      calc ‖x (k + 1 + 1) - x (k + 1)‖ ≤ β * ‖F (x (k + 1))‖ := hA
        _ ≤ β * ((γ + δ) * ‖x (k + 1) - x k‖) := mul_le_mul_of_nonneg_left hB hβ0
        _ = α * ‖x (k + 1) - x k‖ := by rw [hαdef]; ring
        _ ≤ α * (r * α ^ k * (1 - α)) := mul_le_mul_of_nonneg_left ih2 hα0
        _ = r * α ^ (k + 1) * (1 - α) := by ring
  intro k
  exact ⟨hmem k (main k).1, (main k).2⟩
