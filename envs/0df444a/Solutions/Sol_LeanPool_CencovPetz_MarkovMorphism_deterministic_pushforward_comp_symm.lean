-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_comp_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:47.633982+00:00
-- url     : https://prove2.me/submissions/2a90082b-e3a6-4245-b50a-1f469e96bb75

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
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_deterministic_pushforward_apply_of_equiv
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
    (e : α ≃ β) (p : Simplex α) :
    (MarkovMorphism.deterministic (α := β) (β := α)
        (g := (e.symm : β → α))
        e.symm.surjective).pushforward
      ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p)
      = p := by
  classical
  ext a
  -- Evaluate both pushforwards using the explicit
  -- "equivalence" formulas.
  calc
    ((MarkovMorphism.deterministic (α := β) (β := α)
          (g := (e.symm : β → α))
          e.symm.surjective).pushforward
        ((MarkovMorphism.deterministic (α := α) (β := β)
            (g := (e : α → β))
            e.surjective).pushforward p)).p a
        =
          ((MarkovMorphism.deterministic (α := α) (β := β)
              (g := (e : α → β))
              e.surjective).pushforward p).p
            (e a) := by
              simpa using
                (deterministic_pushforward_apply_of_equiv
                  (α := β) (β := α) (e := e.symm)
                  (p :=
                    (MarkovMorphism.deterministic
                      (α := α) (β := β)
                      (g := (e : α → β))
                      e.surjective).pushforward p)
                  (b := a))
    _ = p.p a := by
          simpa using
            (deterministic_pushforward_apply_of_equiv
              (α := α) (β := β) (e := e)
              (p := p) (b := e a))
end LeanPool.CencovPetz.MarkovMorphism
