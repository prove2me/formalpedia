-- Prove2me | solution 1 for NAGFlow.Implicit.last_term_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:27:58.427991+00:00
-- url     : https://prove2.me/submissions/ace37081-028c-471f-84e0-b33cec6daa89

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open NAGFlow.Implicit

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (xstar : V) (γ : ℕ → ℝ) (v : ℕ → V) (k : ℕ) :
    γ k * ⟪v (k + 1) - v k, (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar⟫
      = γ k * ⟪v (k + 1) - v k, v (k + 1) - xstar⟫ - γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 := by
  have e : (1 / 2 : ℝ) • (v (k + 1) + v k) - xstar
      = (v (k + 1) - xstar) - (1 / 2 : ℝ) • (v (k + 1) - v k) := by module
  rw [e, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring
