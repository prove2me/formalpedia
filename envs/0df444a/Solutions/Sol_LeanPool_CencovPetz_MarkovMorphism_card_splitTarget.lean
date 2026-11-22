-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.card_splitTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:06.465234+00:00
-- url     : https://prove2.me/submissions/ae88ec11-086f-4726-ac0d-a5c20098d69d

module
public import Definitions.Def_LeanPool_CencovPetz_SplittingUniform
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_RationalPoint
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_tangentPushforwardLinear_apply
public import Theorems.Thm_LeanPool_CencovPetz_Simplex_uniform_apply
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.MarkovMorphism.tangentPushforwardLinear_apply
attribute [local simp] LeanPool.CencovPetz.Simplex.uniform_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply



set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
universe u
open LeanPool.CencovPetz.MarkovMorphism
variable {α : Type u} [Fintype α]
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (m : α → ℕ) :
    Fintype.card (SplitTarget (α := α) m) = ∑ a : α, m a := by
  classical
  simp [SplitTarget]
end LeanPool.CencovPetz.MarkovMorphism
