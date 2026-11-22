-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.continuous_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:09.469536+00:00
-- url     : https://prove2.me/submissions/d7b940c1-d3a6-490c-80cd-4dc55676d517

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SimplexTopology

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.Simplex
namespace LeanPool.CencovPetz.Simplex
theorem _root_.solution : Continuous fun p : Simplex α => p.p :=
  continuous_induced_dom
end LeanPool.CencovPetz.Simplex
