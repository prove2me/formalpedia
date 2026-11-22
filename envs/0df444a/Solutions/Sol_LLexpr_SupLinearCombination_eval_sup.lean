-- Prove2me | solution 1 for LLexpr.SupLinearCombination.eval_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:37.952582+00:00
-- url     : https://prove2.me/submissions/6a48bf04-5743-427e-8fb2-ca28ff1b47e6

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr

set_option autoImplicit true
@[expose] public section
public section
open LLexpr
open scoped BigOperators
variable {n : ℕ}
open LLexpr.SupLinearCombination
namespace LLexpr.SupLinearCombination
theorem _root_.solution {X : Type*} [AddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [VectorLattice X] (A B : SupLinearCombination n)
    (x : Fin n → X) :
    (A.sup B).eval x = A.eval x ⊔ B.eval x := by
  classical
  unfold eval sup
  rw [Finset.sup'_union]
end LLexpr.SupLinearCombination
