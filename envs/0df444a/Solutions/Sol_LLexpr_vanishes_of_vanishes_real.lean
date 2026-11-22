-- Prove2me | solution 1 for LLexpr.vanishes_of_vanishes_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:22:50.086269+00:00
-- url     : https://prove2.me/submissions/c9570d4c-2317-44ea-b9bf-f7e5447f6394

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_eq_of_forall_real_eq
public import Theorems.Thm_LLexpr_normalize_eval
attribute [local simp] LLexpr.normalize_eval

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
namespace LLexpr
theorem _root_.solution (e : LLexpr n) (h : Vanishes ℝ e)
    (X : Type*) [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] : Vanishes X e := by
  intro x
  have hreal : ∀ r : Fin n → ℝ, (normalize e).pos.eval r = (normalize e).neg.eval r := by
    intro r
    have hr := h r
    rw [← normalize_eval r e, NormalForm.eval] at hr
    exact sub_eq_zero.mp hr
  have hx :=
    SupLinearCombination.eval_eq_of_forall_real_eq (normalize e).pos (normalize e).neg hreal x
  rw [← normalize_eval x e, NormalForm.eval, hx, sub_self]
end LLexpr
