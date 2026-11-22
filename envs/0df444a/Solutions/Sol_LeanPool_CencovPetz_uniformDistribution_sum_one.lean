-- Prove2me | solution 1 for LeanPool.CencovPetz.uniformDistribution_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:20:45.089725+00:00
-- url     : https://prove2.me/submissions/f05e0c1a-5de6-4b6c-80c3-69d8823fb553

module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Definitions.Def_LeanPool_CencovPetz_Uniform

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
namespace LeanPool.CencovPetz
theorem _root_.solution {α : Type u} [Fintype α] [Nonempty α] :
    (∑ a : α, uniformDistribution (α := α) a) = 1 := by
  simp_all
end LeanPool.CencovPetz
