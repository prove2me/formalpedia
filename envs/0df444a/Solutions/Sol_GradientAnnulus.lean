-- Prove2me | solution 1 for GradientAnnulus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:11:36.33777+00:00
-- url     : https://prove2.me/submissions/f5907e8c-fa30-47d1-8b55-bda1b5a6a079

import Definitions.Def_PHigherOrder_FirstOrderEstimateInput
import Definitions.Def_PHigherOrder_GradientAnnulus

set_option autoImplicit false

theorem _root_.solution (p : ℝ) (F : FirstOrderEstimateInput p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 4 ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ x ∈ Metric.ball (0 : Plane) 1, |v x| ≤ 1) → δ < ‖gradient v 0‖ →
        ContDiffOn ℝ 1 v (Metric.ball 0 (2 * τ)) ∧
          ∀ x ∈ Metric.ball (0 : Plane) (2 * τ),
            δ / 2 ≤ ‖gradient v x‖ ∧ ‖gradient v x‖ ≤ F.C₀
              ∧ ‖gradient v x - gradient v 0‖ ≤ δ / 2 := by
  -- Choice of `τ`.  One threshold is wanted, not a `δ` for every `ε`, so solve for it:
  -- `s := δ / (2 * F.C₀)` and `τ := (1/2) * min (1/4) (s ^ (1 / F.kappa))`.
  obtain ⟨s, hsdef⟩ : ∃ t : ℝ, t = δ / (2 * F.C₀) := ⟨_, rfl⟩
  have hCne : F.C₀ ≠ 0 := ne_of_gt F.C₀_pos
  have hs0 : 0 < s := by
    rw [hsdef]
    exact div_pos hδ (by linarith [F.C₀_pos])
  obtain ⟨τ, hτdef⟩ : ∃ t : ℝ, t = 1 / 2 * min (1 / 4) (s ^ (1 / F.kappa)) := ⟨_, rfl⟩
  have hroot0 : 0 < s ^ (1 / F.kappa) := Real.rpow_pos_of_pos hs0 _
  have hτ0 : 0 < τ := by
    rw [hτdef]
    have : 0 < min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) := lt_min (by norm_num) hroot0
    linarith
  have hτ8 : τ ≤ 1 / 8 := by
    rw [hτdef]
    have : min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) ≤ 1 / 4 := min_le_left _ _
    linarith
  have h2τroot : 2 * τ ≤ s ^ (1 / F.kappa) := by
    rw [hτdef]
    have : min (1 / 4 : ℝ) (s ^ (1 / F.kappa)) ≤ s ^ (1 / F.kappa) := min_le_right _ _
    linarith
  -- `(s ^ (1 / κ)) ^ κ = s`, so `C₀ (2τ)^κ ≤ δ/2` -- the paper's choice.
  have hrootpow : (s ^ (1 / F.kappa)) ^ F.kappa = s := by
    rw [← Real.rpow_mul hs0.le, one_div_mul_cancel (ne_of_gt F.kappa_pos), Real.rpow_one]
  have hkey : F.C₀ * (2 * τ) ^ F.kappa ≤ δ / 2 := by
    have hmono : (2 * τ) ^ F.kappa ≤ s := by
      rw [← hrootpow]
      exact Real.rpow_le_rpow (by linarith) h2τroot F.kappa_pos.le
    have := mul_le_mul_of_nonneg_left hmono F.C₀_pos.le
    rw [hsdef] at this
    have hC : F.C₀ * (δ / (2 * F.C₀)) = δ / 2 := by
      field_simp
    rw [hC] at this
    exact this
  -- `τ` is now fixed, from `δ`, `F.kappa` and `F.C₀` alone.  Only now is `v` introduced,
  -- so the uniformity is structural rather than asserted.
  refine ⟨τ, hτ0, by linarith, ?_⟩
  intro v g hph hbd hgrad
  have hsub : Metric.ball (0 : Plane) (2 * τ) ⊆ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.ball_subset_ball (by linarith)
  obtain ⟨hC1, hub, hhol⟩ := F.est v g hph hbd
  refine ⟨hC1.mono hsub, ?_⟩
  intro x hx
  have hx34 : x ∈ Metric.ball (0 : Plane) (3 / 4) := hsub hx
  have h034 : (0 : Plane) ∈ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.mem_ball_self (by norm_num)
  have hxlt : ‖x‖ < 2 * τ := by
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact hx
  -- The displacement bound, which is the third conjunct and drives the other two.
  have hdisp : ‖gradient v x - gradient v 0‖ ≤ δ / 2 := by
    have h3 := hhol x hx34 0 h034
    rw [sub_zero] at h3
    have hpow : ‖x‖ ^ F.kappa ≤ (2 * τ) ^ F.kappa :=
      Real.rpow_le_rpow (norm_nonneg _) hxlt.le F.kappa_pos.le
    have := mul_le_mul_of_nonneg_left hpow F.C₀_pos.le
    linarith
  refine ⟨?_, hub x hx34, hdisp⟩
  -- Lower bound:  the displacement cannot carry `Dv x` down to `δ/2`.
  have htri := norm_sub_norm_le (gradient v 0) (gradient v x)
  rw [norm_sub_rev] at htri
  linarith
