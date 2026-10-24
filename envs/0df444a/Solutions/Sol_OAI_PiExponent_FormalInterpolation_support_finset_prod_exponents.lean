-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_finset_prod_exponents
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:22:12.355136+00:00
-- url     : https://prove2.me/submissions/a59682f7-d5f7-4af5-9630-a346781a85c1

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
open scoped BigOperators

theorem solution
    {ι σ : Type*} [DecidableEq σ] (s : Finset ι)
    (v : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i ∈ s, v i).support) :
    ∃ b : ι → (σ →₀ Nat),
      (∀ i, i ∈ s → b i ∈ (v i).support) ∧ (∑ i ∈ s, b i) = a := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    simp only [Finset.prod_empty] at ha
    have := MvPolynomial.support_monomial_subset (s := (0 : σ →₀ ℕ)) (a := (1 : ℂ)) (by simpa using ha)
    simpa [eq_comm] using this
  | insert j s hj ih =>
    rw [Finset.prod_insert hj] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ ha)
    obtain ⟨b, hb1, hb2⟩ := ih y hy
    refine ⟨Function.update b j x, ?_, ?_⟩
    · intro i hi
      by_cases h : i = j
      · subst h; simpa using hx
      · rw [Function.update_of_ne h]
        exact hb1 i ((Finset.mem_insert.1 hi).resolve_left h)
    · rw [Finset.sum_insert hj, Function.update_self]
      rw [← hb2]; congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
