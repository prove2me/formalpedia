-- Prove2me | solution 1 for NAGFlow.Implicit.eq_75
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:19:47.635017+00:00
-- url     : https://prove2.me/submissions/fa3e725b-9ca6-4413-9486-b3dfd2d7626b

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open NAGFlow.Implicit

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ) (hγ : 0 < γ k)
    (hstep : IsImplicitStep gradf μ α γ x v k) :
    lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k ≤ -α k * lyap f xstar x v γ (k + 1) := by
  obtain ⟨hα, hx, hv, hg⟩ := hstep
  have hμ : 0 ≤ μ := hf.mu_nonneg
  have hαne : α k ≠ 0 := hα.ne'
  have hγne : γ k ≠ 0 := hγ.ne'
  -- the scheme in multiplied-out form
  have hx' : x (k + 1) - x k = α k • (v (k + 1) - x (k + 1)) := by
    have e : x (k + 1) - x k = α k • ((1 / α k) • (x (k + 1) - x k)) := by
      rw [smul_smul, mul_one_div_cancel hαne, one_smul]
    rw [e, hx]
  have hv' : v (k + 1) - v k = (α k / γ k) • (μ • (x (k + 1) - v (k + 1)) - gradf (x (k + 1))) := by
    have e : v (k + 1) - v k = α k • ((1 / α k) • (v (k + 1) - v k)) := by
      rw [smul_smul, mul_one_div_cancel hαne, one_smul]
    rw [e, hv]
    module
  have hγ1 : γ (k + 1) * (1 + α k) = γ k + α k * μ := by
    field_simp at hg
    linarith
  set g := gradf (x (k + 1)) with hgdef
  set u := x (k + 1) - v (k + 1) with hu
  set b := v (k + 1) - xstar with hb
  have hx0 : x k - x (k + 1) = α k • u := by
    have : x k - x (k + 1) = -(x (k + 1) - x k) := by abel
    rw [this, hx', hu, ← neg_sub, smul_neg, neg_neg]
  have hxs : xstar - x (k + 1) = -(u + b) := by
    simp only [hu, hb]; abel
  have hv0 : v k - xstar = b - (α k / γ k) • (μ • u - g) := by
    rw [← hv']
    simp only [hb]; abel
  have hn1 : ‖x k - x (k + 1)‖ ^ 2 = α k ^ 2 * ‖u‖ ^ 2 := by
    rw [hx0, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hg1 : inner ℝ g (x k - x (k + 1)) = α k * inner ℝ g u := by
    rw [hx0, inner_smul_right]
  have hn2 : ‖xstar - x (k + 1)‖ ^ 2 = ‖u‖ ^ 2 + 2 * inner ℝ u b + ‖b‖ ^ 2 := by
    rw [hxs, norm_neg, norm_add_sq_real]
  have hg2 : inner ℝ g (xstar - x (k + 1)) = -(inner ℝ g u + inner ℝ g b) := by
    rw [hxs, inner_neg_right, inner_add_right]
  have hn3 : ‖v k - xstar‖ ^ 2 = ‖b‖ ^ 2 - 2 * (α k / γ k) * (μ * inner ℝ u b - inner ℝ g b)
      + (α k / γ k) ^ 2 * ‖μ • u - g‖ ^ 2 := by
    rw [hv0, norm_sub_sq_real, inner_smul_right, inner_sub_right, inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm u b, real_inner_comm g b]
    ring
  have C1 := hf.mu_convex (x k) (x (k + 1))
  have C2 := hf.mu_convex xstar (x (k + 1))
  rw [← hgdef, hn1, hg1] at C1
  rw [← hgdef, hn2, hg2] at C2
  have C2' := mul_le_mul_of_nonneg_left (ge_iff_le.mp C2) hα.le
  have hR : γ k / 2 * ‖v k - xstar‖ ^ 2 = γ k / 2 * ‖b‖ ^ 2 - α k * (μ * inner ℝ u b - inner ℝ g b)
      + α k ^ 2 / (2 * γ k) * ‖μ • u - g‖ ^ 2 := by
    rw [hn3]
    field_simp
    try ring
  have hN0 : 0 ≤ α k ^ 2 / (2 * γ k) * ‖μ • u - g‖ ^ 2 := by positivity
  have hna0 : 0 ≤ μ * α k * (1 + α k) / 2 * ‖u‖ ^ 2 := by positivity
  have hq : (γ (k + 1) / 2 * ‖b‖ ^ 2) * (1 + α k) = (γ k + α k * μ) / 2 * ‖b‖ ^ 2 := by
    rw [← hγ1]; ring
  unfold lyap
  nlinarith [C1, C2', hR, hN0, hna0, hq]
