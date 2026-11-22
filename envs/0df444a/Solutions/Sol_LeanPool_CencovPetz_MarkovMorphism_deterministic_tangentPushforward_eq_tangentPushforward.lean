-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_eq_tangentPushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.439818+00:00
-- url     : https://prove2.me/submissions/c3b52284-c780-443a-a968-789b94c5dc87

module
public import Definitions.Def_LeanPool_CencovPetz_SufficientStatistic
public import Definitions.Def_LeanPool_CencovPetz_MonotoneMetric
public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Definitions.Def_LeanPool_CencovPetz_LeftInverseIsometry
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_PermutationInvariance
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_apply
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
public import Theorems.Thm_LeanPool_CencovPetz_tangentPushforward_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply
attribute [local simp] LeanPool.CencovPetz.tangentPushforward_apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
variable {α β : Type u} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution [DecidableEq β] (g : α → β)
    (hg : Function.Surjective g) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).tangentPushforward u =
      _root_.LeanPool.CencovPetz.tangentPushforward (α := α) (β := β) g u := by
  ext b
  simpa [_root_.LeanPool.CencovPetz.tangentPushforward_apply] using
    (MarkovMorphism.deterministic_tangentPushforward_apply
      (α := α) (β := β) (g := g) (hg := hg) u b)
end LeanPool.CencovPetz.MarkovMorphism
