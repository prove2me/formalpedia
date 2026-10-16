-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_coordinate_coefficients_imply_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T05:36:28.34316+00:00
-- url     : https://prove2.me/submissions/785823e4-c935-4982-8aa7-eaf9fbc0607f

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ)
    (he : ∀ i, 0 < e i) (n : ℕ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoeff : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, a i / e i : ℕ) < n →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a) Q = 0) :
    Q ∈ Ideal.span (Set.range (fun i : Fin (m + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i)) ^ n := by
  classical
  let I : Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    Ideal.span (Set.range (fun i : Fin (m + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i))
  change Q ∈ I ^ n
  -- Each coordinate contributes its natural quotient to the ideal power.
  have hcoordinate (i : Fin (m + 1)) (k : ℕ) :
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ k ∈
        I ^ (k / e i) := by
    have hgen :
        (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i ∈ I := by
      exact Ideal.subset_span ⟨i, rfl⟩
    have hpow := Ideal.pow_mem_pow hgen (k / e i)
    have hsplit : e i * (k / e i) + k % e i = k := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod k (e i)
    have hfactor :
        (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ k =
          ((MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ e i) ^
              (k / e i) *
            (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ (k % e i) := by
      rw [← pow_mul, ← pow_add, hsplit]
    rw [hfactor]
    exact (I ^ (k / e i)).mul_mem_right _ hpow
  -- Multiplying coordinates adds their contributions.
  have hmonomial (d : Fin (m + 1) →₀ ℕ) (c : ℂ) :
      MvPolynomial.monomial d c ∈ I ^ (∑ i, d i / e i) := by
    have hprod :
        (∏ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ d i) ∈
          ∏ i, I ^ (d i / e i) := by
      apply Ideal.prod_mem_prod
      intro i hi
      exact hcoordinate i (d i)
    rw [Finset.prod_pow_eq_pow_sum] at hprod
    rw [MvPolynomial.monomial_eq,
      Finsupp.prod_fintype d
        (fun i k => (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) ^ k)
        (fun i => pow_zero _)]
    exact (I ^ (∑ i, d i / e i)).mul_mem_left _ hprod
  -- Every exponent in the support lies on or above the staircase boundary.
  rw [MvPolynomial.as_sum Q]
  apply (I ^ n).sum_mem
  intro d hd
  have hbound : n ≤ ∑ i, d i / e i := by
    by_contra hn
    have hz := hcoeff (fun i => d i) (Nat.lt_of_not_ge hn)
    apply (MvPolynomial.mem_support_iff.mp hd)
    simpa only [InterpolationMatrix.exponentVector,
      Finsupp.equivFunOnFinite_symm_coe] using hz
  exact Ideal.pow_le_pow_right hbound (hmonomial d (MvPolynomial.coeff d Q))
