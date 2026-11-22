-- Prove2me | solution 1 for LLexpr.normalize_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:22:14.683348+00:00
-- url     : https://prove2.me/submissions/d0d558f4-ecfc-4414-936f-37579ba4eb6c

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_inf
section
@[expose] public section
namespace LLexpr
open scoped BigOperators
variable {n : ℕ}
section Evaluation
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Evaluation
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Combinations
namespace SupLinearCombination
@[simp] private theorem linearCombination_zero_coeff {X : Type*} [AddCommGroup X]
    [Module ℝ X] (x : Fin n → X) :
    Fintype.linearCombination ℝ x (fun _ : Fin n => 0) = 0 := by
  change Fintype.linearCombination ℝ x (0 : Fin n → ℝ) = 0
  exact map_zero (Fintype.linearCombination ℝ x)
end SupLinearCombination
namespace NormalForm
end NormalForm
end LLexpr
end
end

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
namespace LLexpr
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (x : Fin n → X) (e : LLexpr n) :
    (normalize e).eval x = eval x e := by
  induction e <;> simp [normalize, *]
end LLexpr
