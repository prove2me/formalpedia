-- Prove2me | solution 1 for NAGFlow.Implicit.diff_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:31:46.507014+00:00
-- url     : https://prove2.me/submissions/a5b995a3-4565-431d-9e53-bba37c88ff51

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open NAGFlow.Implicit

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V → ℝ) (xstar : V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ)
    (hα : 0 < α k) (hγ : (γ (k + 1) - γ k) / α k = μ - γ (k + 1)) :
    (lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k
        = f (x (k + 1)) - f (x k) + (γ (k + 1) - γ k) / 2 * ‖v (k + 1) - xstar‖ ^ 2
          + γ k / 2 * (‖v (k + 1) - xstar‖ ^ 2 - ‖v k - xstar‖ ^ 2)) ∧
    (lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k
        = f (x (k + 1)) - f (x k) + α k / 2 * (μ - γ (k + 1)) * ‖v (k + 1) - xstar‖ ^ 2
          + γ k * ⟪v (k + 1) - v k, (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar⟫) := by
  have hα' := hα.ne'
  have hg : γ (k + 1) - γ k = α k * (μ - γ (k + 1)) := by
    field_simp at hγ; linarith
  have hinner : ⟪v (k + 1) - v k, (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar⟫
      = 1 / 2 * (‖v (k + 1) - xstar‖ ^ 2 - ‖v k - xstar‖ ^ 2) := by
    have e1 : (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar
        = (1 / 2 : ℝ) • ((v (k + 1) - xstar) + (v k - xstar)) := by module
    have e2 : v (k + 1) - v k = (v (k + 1) - xstar) - (v k - xstar) := by abel
    rw [e1, e2, real_inner_smul_right, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (v k - xstar)]
    ring
  constructor
  · unfold lyap; ring
  · unfold lyap
    rw [hinner]
    have : (γ (k + 1) - γ k) / 2 = α k / 2 * (μ - γ (k + 1)) := by rw [hg]; ring
    nlinarith [this]
