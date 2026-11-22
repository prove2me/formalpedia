-- Prove2me | solution 1 for LLexpr.NormalForm.eval_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:20:00.567792+00:00
-- url     : https://prove2.me/submissions/e3f24f75-6ffe-47d1-ac15-78ce40414504

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
open LLexpr.NormalForm
namespace LLexpr.NormalForm
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (r : ℝ) (N : NormalForm n)
    (x : Fin n → X) :
    (smul r N).eval x = r • N.eval x := by
  by_cases hr : 0 ≤ r
  · simp [smul, hr, eval, smul_sub]
  · have hneg : 0 ≤ -r := by linarith
    simp [smul, hr, hneg, eval, smul_sub]
    abel
end LLexpr.NormalForm
