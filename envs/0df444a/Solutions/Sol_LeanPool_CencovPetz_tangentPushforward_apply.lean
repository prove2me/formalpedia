-- Prove2me | solution 1 for LeanPool.CencovPetz.tangentPushforward_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:37.102024+00:00
-- url     : https://prove2.me/submissions/567d247d-94d9-4d87-8d59-721422903f9c

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
namespace LeanPool.CencovPetz
theorem _root_.solution (g : α → β) (u : tangentSpace (α := α)) (b : β) :
    (tangentPushforward (α := α) (β := β) g u : β → ℝ) b = ∑ a with g a = b, ((u : α → ℝ) a) :=
  rfl
end LeanPool.CencovPetz
