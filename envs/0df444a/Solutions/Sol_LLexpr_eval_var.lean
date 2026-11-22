-- Prove2me | solution 1 for LLexpr.eval_var
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:12:26.011032+00:00
-- url     : https://prove2.me/submissions/7c67adb4-09ef-49bd-ac25-24b8c4d897f1

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
theorem _root_.solution (x : Fin n → X) (i : Fin n) : eval x (.var i) = x i :=
  rfl
end LLexpr
