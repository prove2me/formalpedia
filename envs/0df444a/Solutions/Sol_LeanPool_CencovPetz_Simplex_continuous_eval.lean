-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.continuous_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:45.793643+00:00
-- url     : https://prove2.me/submissions/8ed85b7b-35ce-4fc8-b2f7-838fff785a96

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_continuous_p

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.Simplex
namespace LeanPool.CencovPetz.Simplex
theorem _root_.solution (a : α) : Continuous fun p : Simplex α => p.p a :=
  (continuous_apply a).comp continuous_p
end LeanPool.CencovPetz.Simplex
