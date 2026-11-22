-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_eq_simplex_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:46.045751+00:00
-- url     : https://prove2.me/submissions/5aecc280-0d7d-47ca-a2b7-a5773090fd49

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
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_apply
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
    (hg : Function.Surjective g) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := α) (β := β) g hg).pushforward p =
      Simplex.pushforward (α := α) (β := β) g hg p := by
  ext b
  simpa [Simplex.pushforward_apply] using
    (MarkovMorphism.deterministic_pushforward_apply (α := α) (β := β) (g := g) (hg := hg) p b)
end LeanPool.CencovPetz.MarkovMorphism
