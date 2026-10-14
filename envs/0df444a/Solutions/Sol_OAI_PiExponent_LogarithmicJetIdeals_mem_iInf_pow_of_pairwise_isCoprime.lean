-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.mem_iInf_pow_of_pairwise_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T10:45:10.477057+00:00
-- url     : https://prove2.me/submissions/ab9cb5e6-cbc0-499e-b855-f543092f28e2

import Mathlib.RingTheory.Ideal.Operations

theorem solution
    {R : Type*} [CommSemiring R] (K n : ℕ) (I : Fin K → Ideal R)
    (hcoprime : ∀ i j : Fin K, i ≠ j → IsCoprime (I i) (I j))
    {x : R} (hx : ∀ i : Fin K, x ∈ (I i) ^ n) :
    x ∈ (⨅ i : Fin K, I i) ^ n := by
  classical
  let s : Finset (Fin K) := Finset.univ
  have hI : (s : Set (Fin K)).Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i hi j hj hij
    exact hcoprime i j hij
  have hpow : (s : Set (Fin K)).Pairwise
      (fun i j => IsCoprime (I i ^ n) (I j ^ n)) := by
    intro i hi j hj hij
    exact (hcoprime i j hij).pow
  have hprod : (∏ i ∈ s, I i) = ⨅ i : Fin K, I i := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hI]
    simp [s]
  have hprod_pow : (∏ i ∈ s, I i ^ n) = ⨅ i : Fin K, I i ^ n := by
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime hpow]
    simp [s]
  have hxinf : x ∈ ⨅ i : Fin K, I i ^ n := Ideal.mem_iInf.mpr hx
  have hxprod : x ∈ ∏ i ∈ s, I i ^ n := by
    rw [hprod_pow]
    exact hxinf
  have hxprod_pow : x ∈ (∏ i ∈ s, I i) ^ n := by
    simpa only [Finset.prod_pow] using hxprod
  rw [hprod] at hxprod_pow
  exact hxprod_pow
