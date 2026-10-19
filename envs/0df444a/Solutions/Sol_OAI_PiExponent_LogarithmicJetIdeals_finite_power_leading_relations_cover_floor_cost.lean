-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_power_leading_relations_cover_floor_cost
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:48:01.535701+00:00
-- url     : https://prove2.me/submissions/00ed4dc3-a501-4c19-8ef7-9b4a55b82ce8

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
    (hdeg : ∀ i, o.degree (f i) = Finsupp.single i (N i))
    (k : ℕ) :
    ∃ S : Finset (MvPolynomial ι 𝕜),
      (∀ g ∈ S, g ∈ I ^ k ∧ o.leadingCoeff g = 1) ∧
      (∀ u : ι → ℕ,
        k ≤ (∑ i, a i * (u i / N i)) →
          ∃ g ∈ S, o.degree g ≤ u) := by
  classical
  let b : (ι → ℕ) → MvPolynomial ι 𝕜 := fun q => ∏ i, f i ^ q i
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h
    have := hlc i
    rw [h, MonomialOrder.leadingCoeff_zero] at this
    exact zero_ne_one this
  have hlcb : ∀ q, o.leadingCoeff (b q) = 1 := by
    intro q
    simp only [b]
    rw [MonomialOrder.leadingCoeff_prod_of_mem_nonZeroDivisors]
    · apply Finset.prod_eq_one
      intro i _
      rw [MonomialOrder.leadingCoeff_pow, hlc i, one_pow]
    · intro i _
      rw [MonomialOrder.leadingCoeff_pow, hlc i, one_pow]
      exact one_mem _
  have hdegb : ∀ q, o.degree (b q) = ∑ i, q i • Finsupp.single i (N i) := by
    intro q
    simp only [b]
    rw [MonomialOrder.degree_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [MonomialOrder.degree_pow, hdeg i]
    · intro i _
      exact pow_ne_zero _ (hf0 i)
  have hbmem : ∀ q, k ≤ ∑ i, a i * q i → b q ∈ I ^ k := by
    intro q hq
    have h1 : b q ∈ ∏ i, (I ^ a i) ^ q i := by
      apply Ideal.prod_mem_prod
      intro i _
      exact Ideal.pow_mem_pow (hmem i) _
    have h2 : (∏ i, (I ^ a i) ^ q i) = I ^ (∑ i, a i * q i) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro i _
      rw [← pow_mul]
    rw [h2] at h1
    exact Ideal.pow_le_pow_right hq h1
  let Qs := (Fintype.piFinset (fun _ : ι => Finset.range (k + 1))).filter
    (fun q => k ≤ ∑ i, a i * q i)
  refine ⟨Qs.image b, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨hbmem q (Finset.mem_filter.mp hq).2, hlcb q⟩
  · intro u hu
    let q : ι → ℕ := fun i => min (u i / N i) k
    have hqk : k ≤ ∑ i, a i * q i := by
      by_cases hex : ∃ j, k < u j / N j
      · obtain ⟨j, hj⟩ := hex
        have hqj : q j = k := min_eq_right hj.le
        calc k ≤ a j * q j := by rw [hqj]; exact Nat.le_mul_of_pos_left k (ha j)
          _ ≤ ∑ i, a i * q i :=
            Finset.single_le_sum (f := fun i => a i * q i) (fun i _ => Nat.zero_le _)
              (Finset.mem_univ j)
      · push Not at hex
        have : ∀ i, q i = u i / N i := fun i => min_eq_left (hex i)
        simp only [this]; exact hu
    refine ⟨b q, Finset.mem_image.mpr ⟨q, ?_, rfl⟩, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, hqk⟩
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _))
    · rw [hdegb q]
      intro j
      simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp only [if_true]
        calc q j * N j ≤ (u j / N j) * N j := Nat.mul_le_mul_right _ (min_le_left _ _)
          _ ≤ u j := Nat.div_mul_le_self (u j) (N j)
      · intro i _ hij; simp [hij]
      · intro h; exact absurd (Finset.mem_univ j) h

