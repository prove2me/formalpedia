-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.monomial_mem_power_of_coordinate_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T21:59:44.561977+00:00
-- url     : https://prove2.me/submissions/c20b65b8-25e7-467c-b9b7-324e947d1b5e

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (n : ℕ)
    (d k : Fin (m + 1) →₀ ℕ)
    (hksum : k.sum (fun _ x => x) = n)
    (hdiv : ∀ i, k i * e i ≤ d i) :
    MvPolynomial.monomial d (1 : ℂ) ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  classical
  let I : Ideal (MvPolynomial (Fin (m + 1)) ℂ) :=
    Ideal.span (Set.range fun i : Fin (m + 1) => MvPolynomial.X i ^ e i)
  have hg (i : Fin (m + 1)) : MvPolynomial.X i ^ e i ∈ I := by
    exact Ideal.subset_span ⟨i, rfl⟩
  have hprod (s : Finset (Fin (m + 1))) :
      (∏ i ∈ s, (MvPolynomial.X i ^ e i) ^ k i) ∈ I ^ (∑ i ∈ s, k i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hg i) (k i)) ih
  let a : (Fin (m + 1)) →₀ ℕ :=
    Finsupp.indicator k.support (fun i _ => k i * e i)
  have halloc :
      (∏ i ∈ k.support, (MvPolynomial.X i ^ e i) ^ k i) ∈ I ^ n := by
    rw [← hksum]
    simpa [Finsupp.sum] using hprod k.support
  have hmonomial :
      (∏ i ∈ k.support, (MvPolynomial.X i ^ e i) ^ k i) =
        MvPolynomial.monomial a (1 : ℂ) := by
    calc
      (∏ i ∈ k.support, (MvPolynomial.X i ^ e i) ^ k i) =
          ∏ i ∈ k.support, MvPolynomial.X i ^ (k i * e i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (pow_mul' (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) ℂ) (k i) (e i)).symm
      _ = MvPolynomial.monomial a (1 : ℂ) := by
        simpa [a] using
          (MvPolynomial.prod_X_pow (fun i => k i * e i) k.support)
  have ha : MvPolynomial.monomial a (1 : ℂ) ∈ I ^ n := by
    rw [← hmonomial]
    exact halloc
  have had : a ≤ d := by
    intro i
    change Finsupp.indicator k.support (fun j _ => k j * e j) i ≤ d i
    by_cases hi : i ∈ k.support
    · rw [Finsupp.indicator_of_mem hi]
      exact hdiv i
    · rw [Finsupp.indicator_of_notMem hi]
      exact Nat.zero_le _
  have hfactor :
      MvPolynomial.monomial d (1 : ℂ) =
        MvPolynomial.monomial a (1 : ℂ) *
          MvPolynomial.monomial (d - a) (1 : ℂ) := by
    rw [← add_tsub_cancel_of_le had, MvPolynomial.monomial_mul]
    simp
  rw [hfactor]
  simpa [mul_comm] using (I ^ n).mul_mem_left
    (MvPolynomial.monomial (d - a) (1 : ℂ)) ha