-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_pushforward_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:01.879745+00:00
-- url     : https://prove2.me/submissions/38bc0b23-fc40-42cb-979a-b4fc403ebe5a

module
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply


attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
open LeanPool.CencovPetz.MarkovMorphism
variable (κ : MarkovMorphism α β)
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution [DecidableEq β] (g : α → β) (hg : Function.Surjective g)
    (p : Simplex α) (b : β) :
    ((deterministic (α := α) (β := β) g hg).pushforward p).p b = ∑ a with g a = b, p.p a := by
  classical
  -- Expand the deterministic kernel, then convert an `if`-sum to a filtered sum.
  have :
      (∑ a : α, if g a = b then p.p a else 0) = ∑ a with g a = b, p.p a := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a : α => g a = b)
        (f := fun a => p.p a)).symm
  simp [deterministic, pushforward, mul_ite, this]
end LeanPool.CencovPetz.MarkovMorphism
