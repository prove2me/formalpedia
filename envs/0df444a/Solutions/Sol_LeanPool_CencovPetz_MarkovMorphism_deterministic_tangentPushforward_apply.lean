-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.deterministic_tangentPushforward_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:23:02.397518+00:00
-- url     : https://prove2.me/submissions/445aca69-22f0-4029-9d1d-d23a3e0ce567

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
theorem _root_.solution [DecidableEq β]
    (g : α → β) (hg : Function.Surjective g)
    (u : tangentSpace (α := α)) (b : β) :
    ((deterministic (α := α) (β := β) g hg).tangentPushforward u : β → ℝ) b =
      ∑ a with g a = b, ((u : α → ℝ) a) := by
  classical
  -- Expand the deterministic kernel, then convert an `if`-sum to a filtered sum.
  have :
      (∑ a : α, if g a = b then (u : α → ℝ) a else 0) = ∑ a with g a = b, (u : α → ℝ) a := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a : α => g a = b)
        (f := fun a => (u : α → ℝ) a)).symm
  simp [deterministic, tangentPushforward, mul_ite, this]
end LeanPool.CencovPetz.MarkovMorphism
