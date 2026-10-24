-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_polynomial_component
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:47:43.244493+00:00
-- url     : https://prove2.me/submissions/4eec8021-3801-4f5d-ad27-674b2e08e822

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (i : Fin d) (q : Polynomial ℂ) (n : Nat)
    (hwi : 0 < w i) :
    MvPolynomial.weightedHomogeneousComponent w (n * w i)
      (Polynomial.aeval (MvPolynomial.X i) q) =
        MvPolynomial.C (q.coeff n) * (MvPolynomial.X i) ^ n := by
  classical
  have hdegree (k : Nat) :
      (k : ℚ) • w i = (n : ℚ) * w i ↔ k = n := by
    constructor
    · intro h
      have h' : (k : ℚ) * w i = (n : ℚ) * w i := by
        simpa [nsmul_eq_mul] using h
      have hcast : (k : ℚ) = (n : ℚ) := by
        exact mul_right_cancel₀ (ne_of_gt hwi) h'
      exact Nat.cast_injective hcast
    · rintro rfl
      simp [nsmul_eq_mul]
  have hterm (k : Nat) :
      MvPolynomial.weightedHomogeneousComponent w (n * w i)
        (MvPolynomial.C (q.coeff k) * (MvPolynomial.X i) ^ k) =
      if k = n then
        MvPolynomial.C (q.coeff k) * (MvPolynomial.X i) ^ k
      else 0 := by
    rw [MvPolynomial.weightedHomogeneousComponent_C_mul]
    by_cases hkn : k = n
    · subst k
      have hdeg : (n : ℚ) * w i = (n : Nat) • w i := by
        simp [nsmul_eq_mul]
      rw [hdeg]
      rw [(MvPolynomial.IsWeightedHomogeneous.pow
        (MvPolynomial.isWeightedHomogeneous_X ℂ w i) n).weightedHomogeneousComponent_same]
      simp
    · have hneq : (n : ℚ) * w i ≠ (k : Nat) • w i := by
        intro heq
        apply hkn
        exact (hdegree k).mp heq.symm
      rw [(MvPolynomial.IsWeightedHomogeneous.pow
        (MvPolynomial.isWeightedHomogeneous_X ℂ w i) k).weightedHomogeneousComponent_ne
          (n * w i) hneq]
      simp [hkn]
  have h_eval :
      Polynomial.aeval (MvPolynomial.X i) q =
        ∑ k ∈ q.support, MvPolynomial.C (q.coeff k) * (MvPolynomial.X i) ^ k := by
    calc
      Polynomial.aeval (MvPolynomial.X i) q =
          Polynomial.aeval (MvPolynomial.X i)
            (∑ k ∈ q.support, Polynomial.C (q.coeff k) * Polynomial.X ^ k) :=
        congrArg (Polynomial.aeval (MvPolynomial.X i))
          (Polynomial.as_sum_support_C_mul_X_pow q)
      _ = ∑ k ∈ q.support, MvPolynomial.C (q.coeff k) * (MvPolynomial.X i) ^ k := by
        simp
  rw [h_eval, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k hk hkn
    simp [hkn]
  · intro hn
    have hcoeff : q.coeff n = 0 := by
      by_contra hcoeff
      exact hn (Polynomial.mem_support_iff.mpr hcoeff)
    simp [hcoeff]