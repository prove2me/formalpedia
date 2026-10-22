-- Prove2me | solution 1 for NAGFlow.GradCorr.eq_93
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:30:01.092577+00:00
-- url     : https://prove2.me/submissions/f2bdb2fc-4321-4259-968e-a8248142483c

import Mathlib
import Definitions.Def_NAGFlow_GradCorr_Setting
set_option autoImplicit false

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (hγ : NAGFlow.PredCorr.IsGammaRun μ α γ)
    (x y v : ℕ → V) (hrun : NAGFlow.GradCorr.IsGCRun gradf μ L α γ x y v) (k : ℕ) :
    NAGFlow.PredCorr.lyapHat f xstar y v γ k - NAGFlow.PredCorr.lyap f xstar x v γ k ≤
      -α k * NAGFlow.PredCorr.lyapHat f xstar y v γ k + α k ^ 2 / (2 * γ k) * ‖gradf (y k)‖ ^ 2 := by
  have hμ := hf.mu_nonneg
  have hgpos : ∀ n, 0 < γ n := by
    intro n
    induction n with
    | zero => exact hγ.gamma0_pos
    | succ n ih =>
      have e := hγ.gamma_eq n
      have han := hγ.alpha_pos n
      have e2 : γ (n+1) * (1 + α n) = γ n + α n * μ := by
        field_simp at e; linarith
      by_contra h
      push_neg at h
      nlinarith [mul_nonneg han.le hμ, mul_nonpos_of_nonpos_of_nonneg h (by linarith : (0:ℝ) ≤ 1 + α n)]
  have ha : 0 < α k := hγ.alpha_pos k
  have hg : 0 < γ k := hgpos k
  have e := hγ.gamma_eq k
  have e2 : γ (k+1) - γ k = α k * (μ - γ (k+1)) := by
    field_simp at e; linarith
  set a := α k with ha_def
  set g := γ k with hg_def
  set g' := γ (k+1) with hg'_def
  set p := gradf (y k) with hp_def
  set e0 := xstar with he0
  set v0 := v k with hv0
  set v1 := v (k+1) with hv1
  set y0 := y k with hy0
  set x0 := x k with hx0
  -- vector relations
  have hy := hrun.y_eq k
  have hv := hrun.v_eq k
  have hyx : y0 - x0 = a • (v0 - y0) := by
    have := congrArg (fun z => a • z) hy
    simp only [smul_smul] at this
    rw [mul_one_div_cancel ha.ne', one_smul] at this
    exact this
  have hvv : g • (v1 - v0) = (a * μ) • (y0 - v1) - a • p := by
    have := congrArg (fun z => (a * g) • z) hv
    simp only [smul_smul, smul_sub] at this
    have h1 : a * g * (1 / a) = g := by field_simp
    have h2 : a * g * (μ / g) = a * μ := by field_simp
    have h3 : a * g * (1 / g) = a := by field_simp
    rw [h1, h2, h3] at this
    simp only [smul_sub]
    exact this
  -- scalar facts
  have hc1 := hf.mu_convex x0 y0
  have hc2 := hf.mu_convex e0 y0
  have hfx : x0 - y0 = -(a • (v0 - y0)) := by rw [← hyx]; abel
  rw [hfx, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hc1
  -- Gram identities
  have hI : ‖v0 - e0‖ ^ 2 = ‖v1 - e0‖ ^ 2 + 2 * inner ℝ (v1 - e0) (v0 - v1) + ‖v0 - v1‖ ^ 2 := by
    have := norm_add_sq_real (v1 - e0) (v0 - v1)
    rw [show v1 - e0 + (v0 - v1) = v0 - e0 by abel] at this
    exact this
  have hII : g * inner ℝ (v1 - e0) (v0 - v1) = a * μ * inner ℝ (v1 - e0) (v1 - y0) + a * inner ℝ (v1 - e0) p := by
    have h : g • (v0 - v1) = (a * μ) • (v1 - y0) + a • p := by
      have := hvv
      simp only [smul_sub] at this ⊢
      linear_combination (norm := module) (-1 : ℝ) • this
    have := congrArg (inner ℝ (v1 - e0)) h
    rw [real_inner_smul_right, inner_add_right, real_inner_smul_right, real_inner_smul_right] at this
    exact this
  have hQ : ‖v1 - y0‖ ^ 2 = ‖v1 - e0‖ ^ 2 - 2 * inner ℝ (v1 - e0) (y0 - e0) + ‖y0 - e0‖ ^ 2 := by
    have := norm_sub_sq_real (v1 - e0) (y0 - e0)
    rw [show v1 - e0 - (y0 - e0) = v1 - y0 by abel] at this
    exact this
  have hK : inner ℝ (v1 - e0) (v1 - y0) = ‖v1 - e0‖ ^ 2 - inner ℝ (v1 - e0) (y0 - e0) := by
    rw [show v1 - y0 = (v1 - e0) - (y0 - e0) by abel, inner_sub_right, real_inner_self_eq_norm_sq]
  have hM : inner ℝ (v1 - e0) p = inner ℝ (v1 - v0) p + inner ℝ (v0 - y0) p + inner ℝ (y0 - e0) p := by
    rw [show v1 - e0 = (v1 - v0) + (v0 - y0) + (y0 - e0) by abel, inner_add_left, inner_add_left]
  have hV : 0 ≤ g ^ 2 * ‖v1 - v0‖ ^ 2 + 2 * g * a * inner ℝ (v1 - v0) p + a ^ 2 * ‖p‖ ^ 2 := by
    have h0 := sq_nonneg ‖g • (v1 - v0) + a • p‖
    rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at h0
    nlinarith [sq_nonneg ‖g • (v1 - v0) + a • p‖]
  -- the sign/order conventions of the two convexity facts
  have hc2' : f e0 - f y0 + inner ℝ (y0 - e0) p ≥ μ / 2 * ‖y0 - e0‖ ^ 2 := by
    have h := hc2
    rw [show e0 - y0 = -(y0 - e0) by abel, inner_neg_right, norm_neg, real_inner_comm] at h
    linarith
  have hc1' : f x0 - f y0 + a * inner ℝ (v0 - y0) p ≥ μ / 2 * (a ^ 2 * ‖v0 - y0‖ ^ 2) := by
    have h := hc1
    rw [real_inner_comm] at h
    linarith
  have hS : inner ℝ (v1 - e0) p = inner ℝ (v1 - v0) p + inner ℝ (v0 - y0) p + inner ℝ (y0 - e0) p := hM
  have hYoung : a ^ 2 / (2 * g) * ‖p‖ ^ 2 ≥ -(a * inner ℝ (v1 - v0) p) - g / 2 * ‖v1 - v0‖ ^ 2 := by
    have : a ^ 2 / (2 * g) * ‖p‖ ^ 2 + a * inner ℝ (v1 - v0) p + g / 2 * ‖v1 - v0‖ ^ 2 =
        (g ^ 2 * ‖v1 - v0‖ ^ 2 + 2 * g * a * inner ℝ (v1 - v0) p + a ^ 2 * ‖p‖ ^ 2) / (2 * g) := by
      field_simp
      ring
    have h2 : 0 ≤ (g ^ 2 * ‖v1 - v0‖ ^ 2 + 2 * g * a * inner ℝ (v1 - v0) p + a ^ 2 * ‖p‖ ^ 2) / (2 * g) :=
      div_nonneg hV (by positivity)
    linarith
  rw [norm_sub_rev v0 v1] at hI
  have hI' := congrArg (fun z => g * z) hI
  have hKe := congrArg (fun z => a * μ * z) hK
  have hQe := congrArg (fun z => a * μ * z) hQ
  have he2 := congrArg (fun z => z * ‖v1 - e0‖ ^ 2) e2
  have hQnn : 0 ≤ a * μ * ‖v1 - y0‖ ^ 2 := by positivity
  have hZnn : 0 ≤ μ * a ^ 2 * ‖v0 - y0‖ ^ 2 := by positivity
  have hc2'' := mul_le_mul_of_nonneg_left hc2' (by positivity : (0:ℝ) ≤ 2 * a)
  unfold NAGFlow.PredCorr.lyapHat NAGFlow.PredCorr.lyap NAGFlow.PredCorr.lyapPt
  have hSa := congrArg (fun z => a * z) hS
  linarith [hc2'', hc1', hI', hII, hKe, hQe, he2, hQnn, hZnn, hYoung, hSa]
