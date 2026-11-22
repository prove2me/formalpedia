-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.split_tangentPushforward_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:59.933095+00:00
-- url     : https://prove2.me/submissions/968b17d9-28b0-4b6f-9316-d1ed60ee06a1

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α]
variable (m : α → ℕ) (hm : ∀ a, 0 < m a)
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (u : tangentSpace (α := α)) (a : α) (i : Fin (m a)) :
    (((split (α := α) m hm).tangentPushforward u : SplitTarget (α := α) m → ℝ) ⟨a, i⟩)
      = (u : α → ℝ) a / (m a : ℝ) := by
  classical
  simp [MarkovMorphism.tangentPushforward_apply, split, mul_ite, div_eq_mul_inv, eq_comm]
end LeanPool.CencovPetz.MarkovMorphism
