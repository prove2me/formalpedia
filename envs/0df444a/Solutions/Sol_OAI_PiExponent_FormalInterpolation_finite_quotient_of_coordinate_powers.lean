-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:51:13.31138+00:00
-- url     : https://prove2.me/submissions/9eacb51d-9e5b-4bd5-83a2-7366fb38787b

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_quotient_of_coordinate_powers_general

theorem solution
    {d : Nat} (J : Ideal (MvPolynomial (Fin d) Complex))
    (hpow : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ MvPolynomial.X i ^ e ∈ J) :
    Module.Finite Complex ((MvPolynomial (Fin d) Complex) ⧸ J) := by
  exact OAI.PiExponent.FormalInterpolation.finite_quotient_of_coordinate_powers_general
    (R := Complex) J hpow