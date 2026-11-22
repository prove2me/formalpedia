-- Prove2me | solution 1 for LeanPool.CencovPetz.Simplex.IsRational.isSplitRepresentable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:43.789631+00:00
-- url     : https://prove2.me/submissions/d990f134-8e13-412c-940e-e6d88e9f0be7

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
open LeanPool.CencovPetz.Simplex
variable {α : Type u} [Fintype α]
namespace LeanPool.CencovPetz.Simplex
namespace IsRational
theorem _root_.solution {p : Simplex α} (hp : IsRational (α := α) p) :
    IsSplitRepresentable (α := α) p := by
  rcases hp with ⟨m, hm, hp⟩
  refine ⟨m, hm, ?_⟩
  simp_all
end IsRational
end LeanPool.CencovPetz.Simplex
