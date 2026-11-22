-- Prove2me | solution 1 for LeanPool.CencovPetz.fisherBilin.pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:08.570961+00:00
-- url     : https://prove2.me/submissions/feb5c235-1696-41fb-8187-eebbee10c2cb

module
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Order
public import Definitions.Def_LeanPool_CencovPetz_Simplex
public import Theorems.Thm_LeanPool_CencovPetz_fisherBilin_apply
attribute [local simp] LeanPool.CencovPetz.fisherBilin.apply

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.CencovPetz
open scoped BigOperators
variable {α : Type*} [Fintype α]
open LeanPool.CencovPetz.fisherBilin
variable (p : Simplex α)
namespace LeanPool.CencovPetz.fisherBilin
theorem _root_.solution (u : tangentSpace (α := α)) (hu : u ≠ 0) :
    0 < fisherBilin p u u := by
  classical
  -- Pick an index where `u` is nonzero.
  have hu_fun : (u : α → ℝ) ≠ (0 : α → ℝ) := by
    simp_all
  have h_not_forall : ¬ ∀ a : α, ((u : α → ℝ) a) = 0 := by
    intro hforall
    apply hu_fun
    funext a
    exact hforall a
  obtain ⟨a0, ha0⟩ : ∃ a0 : α, ((u : α → ℝ) a0) ≠ 0 :=
    (Classical.not_forall).1 h_not_forall
  have hterm_pos : 0 < (((u : α → ℝ) a0) * ((u : α → ℝ) a0)) / p.p a0 := by
    -- `(u a0)^2 / p a0` is positive since `u a0 ≠ 0` and `p a0 > 0`.
    have : 0 < ((u : α → ℝ) a0) * ((u : α → ℝ) a0) := mul_self_pos.2 ha0
    have hp_pos : 0 < p.p a0 := p.pos a0
    -- `x / y = x * (1/y)`.
    simpa [div_eq_mul_inv, mul_assoc] using mul_pos this (inv_pos.2 hp_pos)
  -- All terms are nonnegative, and the `a0` term is positive.
  have h_nonneg : ∀ a : α, 0 ≤ (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a := by
    intro a
    have hp_pos : 0 < p.p a := p.pos a
    have : 0 ≤ ((u : α → ℝ) a) * ((u : α → ℝ) a) := mul_self_nonneg ((u : α → ℝ) a)
    -- divide by a positive number
    exact div_nonneg this (le_of_lt hp_pos)
  -- Use `Finset.sum_pos'` on `Finset.univ`.
  have : 0 < ∑ a : α, (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a := by
    -- Convert `Fintype`-sum to `Finset`-sum and apply positivity.
    simpa using
      (Finset.sum_pos' (s := (Finset.univ : Finset α))
        (f := fun a => (((u : α → ℝ) a) * ((u : α → ℝ) a)) / p.p a)
        (h := fun a _ => h_nonneg a)
        (hs := ⟨a0, by simp, hterm_pos⟩))
  simpa [fisherBilin.apply] using this
end LeanPool.CencovPetz.fisherBilin
