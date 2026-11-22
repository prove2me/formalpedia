-- Prove2me | solution 1 for LeanPool.CencovPetz.MonotoneMetricFamily.comp_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:45.504745+00:00
-- url     : https://prove2.me/submissions/92c6b628-5f75-40b6-9dc3-7a287f5b6dff

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
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_comp_symm
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_comp_symm
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_MonotoneMetricFamily_comp_eq_of_left_inverse
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
open LeanPool.CencovPetz.MonotoneMetricFamily
namespace LeanPool.CencovPetz.MonotoneMetricFamily
theorem _root_.solution
    (G : MonotoneMetricFamily) (e : α ≃ β) (p : Simplex α) :
    (G.g (α := β)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).comp
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforwardLinear)
      = G.g (α := α) p := by
  classical
  let κ : MarkovMorphism α β :=
    MarkovMorphism.deterministic (α := α) (β := β)
      (g := (e : α → β)) e.surjective
  let κ' : MarkovMorphism β α :=
    MarkovMorphism.deterministic (α := β) (β := α)
      (g := (e.symm : β → α)) e.symm.surjective
  refine MonotoneMetricFamily.comp_eq_of_left_inverse
    (G := G) (κ := κ) (κ' := κ') (p := p) ?_ ?_
  · simpa [κ, κ'] using
      MarkovMorphism.deterministic_pushforward_comp_symm
        (α := α) (β := β) (e := e) (p := p)
  · intro u
    simpa [κ, κ'] using
      MarkovMorphism.deterministic_tangentPushforward_comp_symm
        (α := α) (β := β) (e := e) (u := u)
end LeanPool.CencovPetz.MonotoneMetricFamily
