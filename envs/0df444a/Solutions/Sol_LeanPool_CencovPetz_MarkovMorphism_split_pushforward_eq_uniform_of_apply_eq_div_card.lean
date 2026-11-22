-- Prove2me | solution 1 for LeanPool.CencovPetz.MarkovMorphism.split_pushforward_eq_uniform_of_apply_eq_div_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:48.892749+00:00
-- url     : https://prove2.me/submissions/bb51c475-d6cd-417a-823d-288ea6b6a400

module
public import Definitions.Def_LeanPool_CencovPetz_Splitting
public import Definitions.Def_LeanPool_CencovPetz_UniformSimplex
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Definitions.Def_LeanPool_CencovPetz_SplittingUniform
public import Theorems.Thm_LeanPool_CencovPetz_MarkovMorphism_split_pushforward_apply
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
variable {α : Type u} [Fintype α] [Nonempty α]
namespace LeanPool.CencovPetz.MarkovMorphism
theorem _root_.solution (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (p : Simplex α)
    (hp : ∀ a, p.p a = (m a : ℝ) / (Fintype.card (SplitTarget (α := α) m) : ℝ)) :
    letI : Nonempty (SplitTarget (α := α) m) := by
      classical
      rcases (inferInstance : Nonempty α) with ⟨a0⟩
      exact ⟨⟨a0, ⟨0, hm a0⟩⟩⟩
    (split (α := α) m hm).pushforward p = Simplex.uniform (α := SplitTarget (α := α) m) := by
  classical
  ext b
  rcases b with ⟨a, i⟩
  have hm0 : (m a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hm a))
  rw [split_pushforward_apply (α := α) (m := m) (hm := hm) (p := p) (a := a) (i := i)]
  simp [Simplex.uniform_apply, hp a, hm0, div_eq_mul_inv, mul_comm]
end LeanPool.CencovPetz.MarkovMorphism
