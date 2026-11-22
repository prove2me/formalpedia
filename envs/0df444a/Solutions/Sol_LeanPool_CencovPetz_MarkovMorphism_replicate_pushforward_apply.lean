-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.replicate_pushforward_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:24:52.059628+00:00
-- url     : https://prove2.me/submissions/ec960069-21f1-4173-85d8-631a2fed3a2d

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
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
variable {α : Type u} [Fintype α]
open LeanPool.CencovPetz.MarkovMorphism
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (m : ℕ) (hm : 0 < m) (p : Simplex α) (a : α) (i : Fin m) :
    ((replicate (α := α) m hm).pushforward p).p (a, i) = p.p a / m := by
  classical
  -- Only the term `a' = a` contributes.
  simp [MarkovMorphism.pushforward_apply, replicate, mul_ite, div_eq_mul_inv]
end LeanPool.CencovPetz.MarkovMorphism
