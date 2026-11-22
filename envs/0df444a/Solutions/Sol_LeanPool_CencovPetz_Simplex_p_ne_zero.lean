-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.p_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:44.395036+00:00
-- url     : https://prove2.me/submissions/0fb97286-ee70-42cc-99e4-b430b78451dd

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
open LeanPool.CencovPetz.Simplex
variable (p : Simplex α)
namespace LeanPool.CencovPetz.Simplex
theorem _root_.solution (a : α) : p.p a ≠ 0 :=
  ne_of_gt (p.pos a)
end LeanPool.CencovPetz.Simplex
