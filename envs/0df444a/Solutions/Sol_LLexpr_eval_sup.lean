-- Prove2me | solution 1 for LLexpr.eval_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:00.747668+00:00
-- url     : https://prove2.me/submissions/f1df1ada-cc0b-4758-bc9d-4c8a58dc8e15

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
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace LLexpr
theorem _root_.solution (x : Fin n → X) (e₁ e₂ : LLexpr n) :
    eval x (.sup e₁ e₂) = eval x e₁ ⊔ eval x e₂ := rfl
end LLexpr
