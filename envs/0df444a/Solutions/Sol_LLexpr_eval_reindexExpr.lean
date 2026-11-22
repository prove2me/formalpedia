-- Prove2me | solution 1 for LLexpr.eval_reindexExpr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:37.241195+00:00
-- url     : https://prove2.me/submissions/21498480-980e-49ab-b385-8e7c82ab5146

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
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_inf

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace LLexpr
theorem _root_.solution {m n : ℕ} (x : Fin m → X)
    (f : Fin n → Fin m) (e : LLexpr n) :
    eval x (reindexExpr f e) = eval (fun i => x (f i)) e := by
  induction e <;> simp [reindexExpr, *]
end LLexpr
