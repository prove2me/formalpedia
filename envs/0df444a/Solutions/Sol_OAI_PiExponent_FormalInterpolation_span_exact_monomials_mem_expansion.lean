-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_exact_monomials_mem_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:06:39.770976+00:00
-- url     : https://prove2.me/submissions/a0df534f-5e94-425d-bea6-7cce29ef6261

import Mathlib.RingTheory.MvPolynomial.Ideal
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mem_ideal_span_as_finset_sum

open scoped BigOperators

theorem solution
    {σ : Type*} [Fintype σ] {R : Type*} [CommSemiring R]
    (f : σ → R) (n : Nat) (p : R)
    (hp : p ∈ Ideal.span {x : R | ∃ b : σ → Nat, (∑ i, b i) = n ∧ x = ∏ i, f i ^ (b i)}) :
    ∃ (m : Nat) (b : Fin m → σ → Nat) (q : Fin m → R),
      (∀ j, (∑ i, b j i) = n) ∧
      p = ∑ j, (∏ i, f i ^ (b j i)) * q j := by
  obtain ⟨m, x, q, hx, hexp⟩ :=
    OAI.PiExponent.FormalInterpolation.mem_ideal_span_as_finset_sum
      {x : R | ∃ b : σ → Nat, (∑ i, b i) = n ∧ x = ∏ i, f i ^ (b i)} p hp
  classical
  let b : Fin m → σ → Nat := fun j => Classical.choose (hx j)
  refine ⟨m, b, q, ?_, ?_⟩
  · intro j
    exact (Classical.choose_spec (hx j)).1
  · rw [hexp]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [(Classical.choose_spec (hx j)).2]