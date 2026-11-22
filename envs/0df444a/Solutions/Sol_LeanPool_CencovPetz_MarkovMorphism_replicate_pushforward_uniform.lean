-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.replicate_pushforward_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:38.998751+00:00
-- url     : https://prove2.me/submissions/713834a9-3d53-4435-83e1-a2a8455d17e3

module
public import Definitions.Def_LeanPool_CencovPetz_MarkovMorphism
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_Replication
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_replicate_pushforward_apply
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
theorem _root_.solution [Nonempty α] (m : ℕ) (hm : 0 < m) :
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (α × Fin m) := by
        simp_all
    (replicate (α := α) m hm).pushforward (Simplex.uniform (α := α))
      =
      Simplex.uniform (α := α × Fin m) := by
  classical
  ext b
  rcases b with ⟨a, i⟩
  rw [replicate_pushforward_apply (α := α) (m := m) (hm := hm) (p := Simplex.uniform (α := α))
        (a := a) (i := i)]
  simp [Simplex.uniform_apply, div_eq_mul_inv, mul_comm]
end LeanPool.CencovPetz.MarkovMorphism
