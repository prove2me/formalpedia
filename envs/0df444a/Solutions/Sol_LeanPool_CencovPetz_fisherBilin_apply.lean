-- Prove2me | solution 1 for LeanPool.CencovPetz.fisherBilin.apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:41.962207+00:00
-- url     : https://prove2.me/submissions/d1079b1e-7f0f-4655-8c6c-2938148900ac

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
open LeanPool.CencovPetz.fisherBilin
variable (p : Simplex α)
namespace LeanPool.CencovPetz.fisherBilin
theorem _root_.solution (u v : tangentSpace (α := α)) :
    fisherBilin p u v = ∑ a, ((u : α → ℝ) a) * ((v : α → ℝ) a) / p.p a := by
  rfl
end LeanPool.CencovPetz.fisherBilin
