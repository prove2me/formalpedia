-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.mvPolynomial_product_coefficient_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T08:31:27.643969+00:00
-- url     : https://prove2.me/submissions/e9bfb50c-c518-415d-a03f-8b2e64bc132a

import Mathlib.Algebra.MvPolynomial.Basic

open scoped BigOperators

private theorem mvPolynomial_product_coefficient_allocation_aux
    {ι σ R : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [CommSemiring R] (P : ι → MvPolynomial σ R) :
    ∀ (s : Finset ι) (e : σ →₀ Nat),
      MvPolynomial.coeff e (∏ i ∈ s, P i) ≠ 0 →
      ∃ d : ι → σ →₀ Nat,
        (∀ i ∈ s, MvPolynomial.coeff (d i) (P i) ≠ 0) ∧
        (∑ i ∈ s, d i = e) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro e h
      have he : e = 0 := by
        by_contra hn
        apply h
        simp [Finset.prod_empty, MvPolynomial.coeff_one, Ne.symm hn]
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp [he]
  | @insert a s ha ih =>
      intro e h
      have hprod : MvPolynomial.coeff e (P a * ∏ i ∈ s, P i) ≠ 0 := by
        simpa [Finset.prod_insert, ha] using h
      rw [MvPolynomial.coeff_mul] at hprod
      have hex : ∃ z ∈ Finset.antidiagonal e,
          MvPolynomial.coeff z.1 (P a) * MvPolynomial.coeff z.2 (∏ i ∈ s, P i) ≠ 0 := by
        by_contra hn
        have hz : ∀ z ∈ Finset.antidiagonal e,
            MvPolynomial.coeff z.1 (P a) * MvPolynomial.coeff z.2 (∏ i ∈ s, P i) = 0 := by
          intro z hz
          by_contra hne
          exact hn ⟨z, hz, hne⟩
        exact hprod (by rw [Finset.sum_eq_zero hz])
      obtain ⟨z, hz, hterm⟩ := hex
      have hleft : MvPolynomial.coeff z.1 (P a) ≠ 0 := by
        intro hh
        apply hterm
        rw [hh, zero_mul]
      have hright : MvPolynomial.coeff z.2 (∏ i ∈ s, P i) ≠ 0 := by
        intro hh
        apply hterm
        rw [hh, mul_zero]
      obtain ⟨d, hd, hdsum⟩ := ih z.2 hright
      refine ⟨Function.update d a z.1, ?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa using hleft
        · have hia : i ≠ a := fun hEq => ha (hEq ▸ hi)
          simpa [Function.update_of_ne hia] using hd i hi
      · rw [Finset.sum_insert ha]
        change Function.update d a z.1 a +
          (∑ i ∈ s, Function.update d a z.1 i) = e
        have hfirst : Function.update d a z.1 a = z.1 := by simp
        have hsum : (∑ i ∈ s, Function.update d a z.1 i) = ∑ i ∈ s, d i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hia : i ≠ a := fun hEq => ha (hEq ▸ hi)
          simp [Function.update_of_ne hia]
        rw [hfirst, hsum, hdsum]
        exact Finset.mem_antidiagonal.mp hz

theorem solution
    {ι σ R : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [CommSemiring R] (P : ι → MvPolynomial σ R) (e : σ →₀ Nat)
    (h : MvPolynomial.coeff e (∏ i, P i) ≠ 0) :
    ∃ d : ι → σ →₀ Nat,
      (∀ i, MvPolynomial.coeff (d i) (P i) ≠ 0) ∧
      (∑ i, d i = e) := by
  classical
  simpa using mvPolynomial_product_coefficient_allocation_aux P Finset.univ e h
