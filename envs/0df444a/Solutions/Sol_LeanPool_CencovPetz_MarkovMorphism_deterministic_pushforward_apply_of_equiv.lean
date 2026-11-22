-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:00.532626+00:00
-- url     : https://prove2.me/submissions/ddd297ab-7ced-413e-a287-4372d109d87d

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
theorem _root_.solution
    (e : α ≃ β) (p : Simplex α) (b : β) :
    ((MarkovMorphism.deterministic (α := α) (β := β)
        (g := (e : α → β)) e.surjective).pushforward
        p).p b =
      p.p (e.symm b) := by
  classical
  have hs : (Finset.univ.filter fun a : α => e a = b) = {e.symm b} := by
    ext a
    simp [e.eq_symm_apply]
  calc
    ((MarkovMorphism.deterministic (α := α) (β := β)
          (g := (e : α → β))
          e.surjective).pushforward p).p b
        = ∑ a with e a = b, p.p a := by
              simpa using
                (MarkovMorphism.deterministic_pushforward_apply
                  (α := α) (β := β) (g := (e : α → β))
                  (hg := e.surjective) p b)
    _ = p.p (e.symm b) := by simp [hs]
end LeanPool.CencovPetz.MarkovMorphism
