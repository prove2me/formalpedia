-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_power_representative_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:05:44.844883+00:00
-- url     : https://prove2.me/submissions/9b08df5b-a7af-46ab-912b-4a10d5d2b967

import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

open scoped BigOperators
theorem solution
    {m : Nat}
    (J : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (N : Nat)
    (hN : 0 < N)
    (i : Fin (m + 1))
    (n : Nat)
    (c : Fin N → Complex)
    (hpow : MvPolynomial.X i ^ N -
      ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val ∈ J)
    (ih : ∀ r : Nat, r < n →
      ∃ R : MvPolynomial (Fin (m + 1)) Complex,
        (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
          MvPolynomial.monomial (Finsupp.single i r) (1 : Complex) - R ∈ J) :
    ∃ R : MvPolynomial (Fin (m + 1)) Complex,
      (∀ b ∈ R.support, b i < N ∧ ∀ j : Fin (m + 1), j ≠ i → b j = 0) ∧
        MvPolynomial.monomial (Finsupp.single i n) (1 : Complex) - R ∈ J := by
  classical
  by_cases hn : n < N
  · refine ⟨MvPolynomial.monomial (Finsupp.single i n) 1, ?_, by simp⟩
    intro b hb
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hb
    subst hb
    refine ⟨by simpa using hn, fun j hj => ?_⟩
    simp [Finsupp.single_apply, Ne.symm hj]
  · push Not at hn
    have hk : ∀ k : Fin N, n - N + k.val < n := fun k => by have := k.isLt; omega
    choose R hRsupp hRmem using fun k : Fin N => ih (n - N + k.val) (hk k)
    refine ⟨∑ k : Fin N, c k • R k, ?_, ?_⟩
    · intro b hb
      obtain ⟨k, -, hbk⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hb)
      exact hRsupp k b (MvPolynomial.support_smul hbk)
    · have hX : ∀ r, MvPolynomial.monomial (Finsupp.single i r) (1 : ℂ) = MvPolynomial.X i ^ r :=
        fun r => (MvPolynomial.X_pow_eq_monomial).symm
      have hid : MvPolynomial.monomial (Finsupp.single i n) (1 : ℂ) - ∑ k : Fin N, c k • R k =
          MvPolynomial.X i ^ (n - N) * (MvPolynomial.X i ^ N -
            ∑ k : Fin N, MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val) +
          ∑ k : Fin N, MvPolynomial.C (c k) *
            (MvPolynomial.monomial (Finsupp.single i (n - N + k.val)) (1 : ℂ) - R k) := by
        simp only [hX, MvPolynomial.smul_eq_C_mul, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
        have h1 : MvPolynomial.X i ^ (n - N) * MvPolynomial.X i ^ N =
            (MvPolynomial.X i ^ n : MvPolynomial (Fin (m + 1)) ℂ) := by
          rw [← pow_add, Nat.sub_add_cancel hn]
        have h2 : ∑ k : Fin N, MvPolynomial.X i ^ (n - N) * (MvPolynomial.C (c k) * MvPolynomial.X i ^ k.val) =
            ∑ k : Fin N, MvPolynomial.C (c k) * (MvPolynomial.X i ^ (n - N + k.val) : MvPolynomial (Fin (m + 1)) ℂ) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [pow_add]; ring
        rw [h1, h2]
        abel
      rw [hid]
      refine J.add_mem (J.mul_mem_left _ hpow) (J.sum_mem (fun k _ => J.mul_mem_left _ (hRmem k)))
