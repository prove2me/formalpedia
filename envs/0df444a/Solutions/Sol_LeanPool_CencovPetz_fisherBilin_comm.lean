-- Prove2me | solution 1 for LeanPool.CencovPetz.fisherBilin.comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:09.069185+00:00
-- url     : https://prove2.me/submissions/09a250da-bc29-46ce-be3a-cbdcf8ae873b

module
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply

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
    fisherBilin p u v = fisherBilin p v u := by
  classical
  simp [fisherBilin.apply, mul_comm]
end LeanPool.CencovPetz.fisherBilin
