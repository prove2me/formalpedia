-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:22:26.19017+00:00
-- url     : https://prove2.me/submissions/9b622b95-b46d-4e84-bcba-c465d8fdfbe7

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism
variable (κ : MarkovMorphism α β)
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (u : tangentSpace (α := α)) :
    κ.tangentPushforwardLinear u = κ.tangentPushforward u :=
  rfl
end LeanPool.CencovPetz.MarkovMorphism
