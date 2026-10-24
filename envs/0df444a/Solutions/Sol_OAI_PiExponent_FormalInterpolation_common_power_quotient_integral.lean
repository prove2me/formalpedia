-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.common_power_quotient_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:51.766615+00:00
-- url     : https://prove2.me/submissions/a50720de-9b51-48b4-a048-5e49b7f62b9a

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib

open scoped BigOperators

variable {N : Nat}

open MeasureTheory Filter Topology in

theorem solution {d : Nat} (J : Ideal (MvPolynomial (Fin d) ℂ)) (hN : 0 < N) (hpow : ∀ i : Fin d, (MvPolynomial.X i) ^ N ∈ J) : Algebra.IsIntegral ℂ ((MvPolynomial (Fin d) ℂ) ⧸ J) := by
  constructor
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul]
    refine hp.mul (IsIntegral.of_pow hN ?_)
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (hpow i)]; exact isIntegral_zero
