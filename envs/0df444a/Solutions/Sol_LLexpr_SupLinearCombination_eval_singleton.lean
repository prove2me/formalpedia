-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:27.346972+00:00
-- url     : https://prove2.me/submissions/4f261aaa-e428-4825-988a-bc6f4dd996d7

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
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
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
open LLexpr.SupLinearCombination
namespace LLexpr.SupLinearCombination
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (a : Fin n → ℝ) (x : Fin n → X) :
    (singleton a).eval x = Fintype.linearCombination ℝ x a := by
  simp [eval, singleton]
end LLexpr.SupLinearCombination
