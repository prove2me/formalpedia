-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_eq_of_forall_real_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:11.761901+00:00
-- url     : https://prove2.me/submissions/1a836446-5311-497c-a7ed-a5dcba52c2f0

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_le_of_forall_real_le

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
open LLexpr.SupLinearCombination
namespace LLexpr.SupLinearCombination
theorem _root_.solution {X : Type*} [AddCommGroup X]
    [Lattice X] [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (h : ∀ r : Fin n → ℝ, A.eval r = B.eval r) (x : Fin n → X) :
    A.eval x = B.eval x :=
  le_antisymm (eval_le_of_forall_real_le A B (fun r => (h r).le) x)
    (eval_le_of_forall_real_le B A (fun r => (h r).ge) x)
end LLexpr.SupLinearCombination
