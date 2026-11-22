-- Prove2me | solution 1 for LLexpr.eval_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:26.502899+00:00
-- url     : https://prove2.me/submissions/f21baa6f-0d0f-4ed0-963a-d24e4d9069a6

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
theorem _root_.solution (x : Fin n → X) (r : ℝ) (e : LLexpr n) :
    eval x (.smul r e) = r • eval x e := rfl
end LLexpr
