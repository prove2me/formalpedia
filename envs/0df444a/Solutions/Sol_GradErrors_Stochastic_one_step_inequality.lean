-- Prove2me | solution 1 for GradErrors.Stochastic.one_step_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:57:13.085004+00:00
-- url     : https://prove2.me/submissions/871b1ddb-a119-4635-b370-8b44ea52aca3

import Mathlib

set_option autoImplicit false

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace

open scoped RealInnerProductSpace in
theorem gecs_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem gecs_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [gecs_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem gecs_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := gecs_line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hL : LipschitzWith L (gradient f)) (x s w : EuclideanSpace ℝ (Fin n))
    (γ c₁ c₂ : ℝ) (hγ : 0 < γ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h41a : c₁ * ‖gradient f x‖ ^ 2 ≤ -⟪gradient f x, s⟫_ℝ)
    (h41b : ‖s‖ ≤ c₂ * (1 + ‖gradient f x‖))
    (hγsmall : γ * (2 * (L : ℝ) * c₂ ^ 2) ≤ c₁ / 2) :
    f (x + γ • (s + w)) ≤ f x - γ * (c₁ / 2) * ‖gradient f x‖ ^ 2 + γ * ⟪gradient f x, w⟫_ℝ
      + γ ^ 2 * (2 * (L : ℝ) * c₂ ^ 2) + γ ^ 2 * (L : ℝ) * ‖w‖ ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hgrad : ∀ a b, ‖gradient f a - gradient f b‖ ≤ (L : ℝ) * ‖a - b‖ := by
    intro a b
    have := hL.dist_le_mul a b
    simpa [dist_eq_norm] using this
  have hd := gecs_descent hdiff hgrad x (x + γ • (s + w))
  have hyx : x + γ • (s + w) - x = γ • (s + w) := by abel
  rw [hyx] at hd
  rw [real_inner_smul_right, inner_add_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hγ] at hd
  set G := ‖gradient f x‖ with hG
  set S := ‖s‖ with hS
  set W := ‖w‖ with hW
  set N := ‖s + w‖ with hN
  set I := ⟪gradient f x, s⟫_ℝ with hI
  set J := ⟪gradient f x, w⟫_ℝ with hJ
  set Lr : ℝ := (L : ℝ) with hLr
  have hLr0 : 0 ≤ Lr := L.2
  have hG0 : 0 ≤ G := norm_nonneg _
  have hS0 : 0 ≤ S := norm_nonneg _
  have hW0 : 0 ≤ W := norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNle : N ≤ S + W := norm_add_le s w
  have hN2 : N ^ 2 ≤ 2 * S ^ 2 + 2 * W ^ 2 := by nlinarith [sq_nonneg (S - W)]
  have hS2 : S ^ 2 ≤ 2 * c₂ ^ 2 * (1 + G ^ 2) := by
    have h1 : S ^ 2 ≤ (c₂ * (1 + G)) ^ 2 := pow_le_pow_left₀ hS0 h41b 2
    nlinarith [sq_nonneg (1 - G)]
  have hq1 : Lr / 2 * (γ * N) ^ 2 ≤ Lr * γ ^ 2 * S ^ 2 + Lr * γ ^ 2 * W ^ 2 := by
    have : (γ * N) ^ 2 = γ ^ 2 * N ^ 2 := by ring
    rw [this]
    have hg2 : 0 ≤ Lr * γ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hN2 hg2]
  have hq2 : Lr * γ ^ 2 * S ^ 2 ≤ γ ^ 2 * (2 * Lr * c₂ ^ 2) + γ ^ 2 * (2 * Lr * c₂ ^ 2) * G ^ 2 := by
    have hg2 : 0 ≤ Lr * γ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS2 hg2]
  have hq3 : γ ^ 2 * (2 * Lr * c₂ ^ 2) * G ^ 2 ≤ γ * (c₁ / 2) * G ^ 2 := by
    have hgG : 0 ≤ γ * G ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hγsmall hgG
    nlinarith
  have hq4 : γ * I ≤ -(γ * (c₁ * G ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h41a hγ.le
    linarith
  nlinarith
