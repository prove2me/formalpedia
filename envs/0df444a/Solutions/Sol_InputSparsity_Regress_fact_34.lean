-- Prove2me | solution 1 for InputSparsity.Regress.fact_34
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T15:45:17.572879+00:00
-- url     : https://prove2.me/submissions/92db301e-fdad-4318-b360-902dbd39a560

import Mathlib
import Definitions.Def_InputSparsity_Regress_Basic

set_option autoImplicit false
open Matrix
theorem solution {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) (h : Cᵀ * D = 0) :
    InputSparsity.Embed.frobSq (C + D) = InputSparsity.Embed.frobSq C + InputSparsity.Embed.frobSq D := by
  have hc : ∀ j : Fin m, ∑ i : Fin n, C i j * D i j = 0 := by
    intro j
    have hh := congrFun (congrFun h j) j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using hh
  have hcol : ∀ j : Fin m, (∑ i : Fin n, (C i j + D i j)^2) =
      (∑ i : Fin n, C i j ^ 2) + (∑ i : Fin n, D i j ^ 2) := by
    intro j
    calc
      _ = ∑ i : Fin n, (C i j ^ 2 + D i j ^ 2 + 2 * (C i j * D i j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hc j]
        ring
  unfold InputSparsity.Embed.frobSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i j => C i j ^ 2),
    Finset.sum_comm (f := fun i j => D i j ^ 2), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j hj => hcol j)

#print axioms solution
namespace InputSparsity.Regress
open Matrix

example {n m : ℕ} (C D : Matrix (Fin n) (Fin m) ℝ) (h : Cᵀ * D = 0) :
    InputSparsity.Embed.frobSq (C + D) = InputSparsity.Embed.frobSq C + InputSparsity.Embed.frobSq D := by
  exact solution C D h

end InputSparsity.Regress

#print axioms solution
