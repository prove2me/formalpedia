-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.uniform_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:26.726515+00:00
-- url     : https://prove2.me/submissions/a6455945-8633-4bf3-af2d-fe5cfb09ada5

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Definitions.Def_LeanPool_CencovPetz_Uniform
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α] [Nonempty α]
open LeanPool.CencovPetz.Simplex
namespace LeanPool.CencovPetz.Simplex
theorem _root_.solution (a : α) :
    (uniform (α := α)).p a = 1 / (Fintype.card α : ℝ) :=
  rfl
end LeanPool.CencovPetz.Simplex
