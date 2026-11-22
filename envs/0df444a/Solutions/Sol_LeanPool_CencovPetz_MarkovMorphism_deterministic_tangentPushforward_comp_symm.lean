-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_comp_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:48.083445+00:00
-- url     : https://prove2.me/submissions/f814ba8c-8f6a-4cb5-9a3f-31075e368050

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
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_tangentPushforward_apply_of_equiv
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
theorem _root_.solution
    (e : α ≃ β) (u : tangentSpace (α := α)) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).tangentPushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).tangentPushforward u)
      = u := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).tangentPushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).tangentPushforward
            u) : α → ℝ) a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).tangentPushforward
              u : β → ℝ)
            (e a) := by
              simpa using
                (deterministic_tangentPushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (u :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).tangentPushforward u)
                  (b := a))
    _ = (u : α → ℝ) a := by
          simpa using
            (deterministic_tangentPushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (u := u) (b := e a))
end LeanPool.CencovPetz.MarkovMorphism
