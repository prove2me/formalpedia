-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_aux_a9fbb753_463b_437c_88bf_627d1569d537
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T10:09:49.854223+00:00
-- url     : https://prove2.me/submissions/956fe261-e293-49cb-acbd-d0e191843096

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinate_powers_common_exponent
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_common_coordinate_power

open scoped BigOperators

theorem solution
    {d : Nat} (J : Ideal (MvPolynomial (Fin d) ℂ))
    (hpow : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (MvPolynomial.X i) ^ e ∈ J) :
    Module.Finite ℂ ((MvPolynomial (Fin d) ℂ) ⧸ J) := by
  obtain ⟨N, hN, hcommon⟩ :=
    OAI.PiExponent.FormalInterpolation.coordinate_powers_common_exponent J hpow
  exact
    OAI.PiExponent.FormalInterpolation.finite_quotient_of_common_coordinate_power
      J hN hcommon