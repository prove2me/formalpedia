-- Prove2me | solution 1 for LeanPool.CencovPetz.tangentSpace.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:30.934698+00:00
-- url     : https://prove2.me/submissions/77c2bfe4-9c6a-44e4-98fa-44f52246c016

module
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_Simplex

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α]
open LeanPool.CencovPetz.tangentSpace
variable (α)
namespace LeanPool.CencovPetz.tangentSpace
theorem _root_.solution {u : α → ℝ} :
    u ∈ tangentSpace (α := α) ↔ (∑ a, u a) = 0 := by
  simp [tangentSpace, sumLinearMap]
end LeanPool.CencovPetz.tangentSpace
