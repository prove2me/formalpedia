-- Prove2me | solution 1 for LLexpr.eval_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:29.954677+00:00
-- url     : https://prove2.me/submissions/7f3a952d-50d7-41c8-b570-b1f26eb7eb23

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
    eval x (.inf e₁ e₂) = eval x e₁ ⊓ eval x e₂ := rfl
end LLexpr
