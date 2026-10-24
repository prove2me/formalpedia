-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_from_nonzero_scalar_mem
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:03:20.886746+00:00
-- url     : https://prove2.me/submissions/4cd79d4b-d469-46e3-af8c-7752f16b3f0a

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open MvPolynomial

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ)) (i : Fin d)
    (n : Nat) (c : ℂ) (hc : c ≠ 0)
    (h : MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I) :
    ∃ N : Nat, 0 < N ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N ∈ I := by
  have hx : (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ I := by
    have hm := Ideal.mul_mem_left I (MvPolynomial.C c⁻¹) h
    have heq :
        MvPolynomial.C c⁻¹ *
            (MvPolynomial.C c * (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n) =
          (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n := by
      calc
        _ = (MvPolynomial.C c⁻¹ * MvPolynomial.C c) *
              (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n := by rw [← mul_assoc]
        _ = MvPolynomial.C (c⁻¹ * c) *
              (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n := by rw [← map_mul]
        _ = (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n := by
          rw [inv_mul_cancel₀ hc, map_one, one_mul]
    rw [← heq]
    exact hm
  have hmul := Ideal.mul_mem_left I (MvPolynomial.X i) hx
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  simpa [pow_succ, mul_comm] using hmul