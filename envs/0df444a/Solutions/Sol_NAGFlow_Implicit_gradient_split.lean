-- Prove2me | solution 1 for NAGFlow.Implicit.gradient_split
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:31:44.385596+00:00
-- url     : https://prove2.me/submissions/96918bcf-6c74-4a3d-a20d-af0b929045da

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

set_option autoImplicit false
open scoped RealInnerProductSpace
open NAGFlow.Implicit

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (gradf : V → V) (xstar : V) (α : ℕ → ℝ) (x v : ℕ → V) (k : ℕ)
    (hα : 0 < α k) (hx : (1 / α k) • (x (k + 1) - x k) = v (k + 1) - x (k + 1)) :
    -α k * ⟪gradf (x (k + 1)), v (k + 1) - xstar⟫
      = -⟪gradf (x (k + 1)), x (k + 1) - x k⟫
        - α k * ⟪gradf (x (k + 1)), x (k + 1) - xstar⟫ := by
  have e : v (k + 1) - xstar = (1 / α k) • (x (k + 1) - x k) + (x (k + 1) - xstar) := by
    rw [hx]; abel
  rw [e, inner_add_right, real_inner_smul_right]
  field_simp
  ring
