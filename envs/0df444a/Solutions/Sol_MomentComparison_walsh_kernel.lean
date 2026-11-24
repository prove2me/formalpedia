-- Prove2me | solution 1 for MomentComparison.walsh_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:06:12.199429+00:00
-- url     : https://prove2.me/submissions/da322d32-374b-4c4d-b114-9f2331ae1806

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_cubeAverage_const
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.cubeAverage_const

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (x y : Cube n) :
    (∑ s : Finset (Fin n), walsh s x * walsh s y) = if x = y then (2 : ℝ)^n else 0 := by
  have hprod : (∑ s : Finset (Fin n), walsh s x * walsh s y) =
      ∏ i : Fin n, (cubeSign x i * cubeSign y i + 1) := by
    rw [Fintype.prod_add]
    simp only [prod_const_one, mul_one, walsh, prod_mul_distrib]
  rw [hprod]
  by_cases h : x = y
  · subst y
    simp [cubeSign_mul_self, show (1 : ℝ) + 1 = 2 by norm_num]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! he
      exact h (funext he)
    refine prod_eq_zero (mem_univ i) ?_
    cases hx : x i <;> cases hy : y i <;> simp_all [cubeSign]
end MomentComparison
