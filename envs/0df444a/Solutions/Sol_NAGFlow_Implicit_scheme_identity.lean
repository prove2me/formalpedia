-- Prove2me | solution 1 for NAGFlow.Implicit.scheme_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:31:45.442913+00:00
-- url     : https://prove2.me/submissions/ed791bb7-f06c-4b27-855a-0bbca3c89f8c

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open NAGFlow.Implicit

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (gradf : V → V) (xstar : V) (μ : ℝ) (α γ : ℕ → ℝ) (x v : ℕ → V)
    (k : ℕ) (hα : 0 < α k) (hγ : 0 < γ k)
    (hv : (1 / α k) • (v (k + 1) - v k)
      = (μ / γ k) • (x (k + 1) - v (k + 1)) - (1 / γ k) • gradf (x (k + 1))) :
    γ k * ⟪v (k + 1) - v k, v (k + 1) - xstar⟫
      = μ * α k * ⟪x (k + 1) - v (k + 1), v (k + 1) - xstar⟫
        - α k * ⟪gradf (x (k + 1)), v (k + 1) - xstar⟫ := by
  have h := congrArg (fun z => ⟪z, v (k + 1) - xstar⟫) hv
  simp only [real_inner_smul_left, inner_sub_left] at h
  have hα' := hα.ne'
  have hγ' := hγ.ne'
  simp only [inner_sub_left]
  field_simp at h
  linear_combination h
