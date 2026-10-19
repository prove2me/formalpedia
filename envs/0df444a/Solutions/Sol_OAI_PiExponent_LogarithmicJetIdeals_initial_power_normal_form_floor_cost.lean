-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.initial_power_normal_form_floor_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:41:41.380462+00:00
-- url     : https://prove2.me/submissions/f42966e9-2178-4560-bb75-a031e6f36657

import Mathlib
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators


theorem solution
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (I : Ideal (MvPolynomial ι 𝕜))
    (o : MonomialOrder ι)
    (a N : ι → ℕ) (f : ι → MvPolynomial ι 𝕜)
    (ha : ∀ i, 0 < a i) (hN : ∀ i, 0 < N i)
    (hmem : ∀ i, f i ∈ I ^ a i)
    (hlc : ∀ i, o.leadingCoeff (f i) = 1)
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i)) :
    ∀ k : ℕ, ∀ P : MvPolynomial ι 𝕜,
      ∃ Q : MvPolynomial ι 𝕜,
        (∀ u ∈ Q.support,
          (∑ i, a i * (u i / N i)) < k) ∧
        P - Q ∈ I ^ k := by
  classical
  intro k P
  let J := {q : ι → ℕ // k ≤ ∑ i, a i * q i}
  let b : J → MvPolynomial ι 𝕜 := fun q => ∏ i, f i ^ q.1 i
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h
    have := hlc i
    rw [h, MonomialOrder.leadingCoeff_zero] at this
    exact zero_ne_one this
  have hlcb : ∀ q : J, o.leadingCoeff (b q) = 1 := by
    intro q
    simp only [b]
    rw [MonomialOrder.leadingCoeff_prod_of_mem_nonZeroDivisors]
    · apply Finset.prod_eq_one
      intro i _
      rw [MonomialOrder.leadingCoeff_pow, hlc i, one_pow]
    · intro i _
      rw [MonomialOrder.leadingCoeff_pow, hlc i, one_pow]
      exact one_mem _
  have hdegb : ∀ q : J, o.degree (b q) = ∑ i, q.1 i • Finsupp.single i (N i) := by
    intro q
    simp only [b]
    rw [MonomialOrder.degree_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [MonomialOrder.degree_pow, hdeg i]
    · intro i _
      exact pow_ne_zero _ (hf0 i)
  have hbmem : ∀ q : J, b q ∈ I ^ k := by
    intro q
    have h1 : b q ∈ ∏ i, (I ^ a i) ^ q.1 i := by
      apply Ideal.prod_mem_prod
      intro i _
      exact Ideal.pow_mem_pow (hmem i) _
    have h2 : (∏ i, (I ^ a i) ^ q.1 i) = I ^ (∑ i, a i * q.1 i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul]
    rw [h2] at h1
    exact Ideal.pow_le_pow_right q.2 h1
  obtain ⟨g, r, hfr, -, hr⟩ := o.div (b := b) (fun q => by rw [hlcb q]; exact isUnit_one) P
  refine ⟨r, ?_, ?_⟩
  · intro u hu
    by_contra hcon
    push Not at hcon
    let q : J := ⟨fun i => u i / N i, by
      simpa [mul_comm] using hcon⟩
    apply hr u hu q
    rw [hdegb q]
    intro j
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp only [if_true]
      exact Nat.div_mul_le_self (u j) (N j)
    · intro i _ hij; simp [hij]
    · intro h; exact absurd (Finset.mem_univ j) h
  · have : P - r = Finsupp.linearCombination _ b g := by
      rw [hfr]; ring
    rw [this, Finsupp.linearCombination_apply]
    apply Ideal.sum_mem
    intro q _
    show g q • b q ∈ I ^ k
    rw [smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hbmem q)

