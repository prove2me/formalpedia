-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eulerDerivation_nonzero_constant_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T05:06:46.355439+00:00
-- url     : https://prove2.me/submissions/160847fb-d1c7-4be5-8e30-c783e24f6460

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Derivation.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerDerivation_fraction_formula
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eulerPolynomial_no_nonzero_constant_of_denominator_ne_zero

open RatFunc

theorem solution
    (K : Type) [Field K] [CharZero K]
    (d : Derivation K (RatFunc K) (RatFunc K))
    (hdX : d RatFunc.X = RatFunc.X) :
    ∀ (r : RatFunc K) (c : K), c ≠ 0 →
      d r ≠ algebraMap K (RatFunc K) c := by
  intro r c hc hEq
  obtain ⟨p, q, hr, hq, hcop, hformula⟩ :=
    OAI.PiExponent.FormalInterpolation.eulerDerivation_fraction_formula
      (K := K) d hdX r
  have hformula' := hformula
  rw [hEq] at hformula'
  exact OAI.PiExponent.FormalInterpolation.eulerPolynomial_no_nonzero_constant_of_denominator_ne_zero
    (K := K) p q hq hcop c hc hformula'