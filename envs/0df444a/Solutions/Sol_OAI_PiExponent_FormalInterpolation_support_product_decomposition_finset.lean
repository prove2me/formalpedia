-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.support_product_decomposition_finset
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:26:26.837233+00:00
-- url     : https://prove2.me/submissions/44511699-b838-4cc5-ae97-15030e7c07b3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators Pointwise

theorem solution
    {σ ι : Type*} [DecidableEq σ]
    (s : Finset ι) (f : ι → MvPolynomial σ Complex) (a : σ →₀ Nat)
    (ha : a ∈ (∏ i ∈ s, f i).support) :
    ∃ b : ι → σ →₀ Nat,
      (∀ i, i ∈ s → b i ∈ (f i).support) ∧ a = ∑ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty =>
      have ha0 : a = 0 := by simpa using ha
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i hi
        simp at hi
      · simpa [ha0]
  | @insert i s his ih =>
      have hprod : (∏ j ∈ insert i s, f j) = f i * (∏ j ∈ s, f j) := by
        simp [his]
      rw [hprod] at ha
      have hmem : a ∈ (f i).support + (∏ j ∈ s, f j).support :=
        MvPolynomial.support_mul _ _ ha
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hmem
      obtain ⟨b, hb, hbsum⟩ := ih y hy
      refine ⟨Function.update b i x, ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hjs
        · subst j
          simpa [Function.update] using hx
        · have hne : j ≠ i := by
            intro h
            subst j
            exact his hjs
          simpa [Function.update, hne] using hb j hjs
      · rw [Finset.sum_insert his]
        have hsame : Function.update b i x i = x := by
          simp [Function.update]
        rw [hsame]
        have hsum : (∑ j ∈ s, Function.update b i x j) = ∑ j ∈ s, b j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hne : j ≠ i := by
            intro h
            subst j
            exact his hj
          simp [Function.update, hne]
        rw [hsum]
        calc
          a = x + y := hxy.symm
          _ = x + ∑ j ∈ s, b j := by rw [hbsum]