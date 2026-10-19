-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_power_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T08:15:36.704663+00:00
-- url     : https://prove2.me/submissions/8cd77e9f-d2df-4d16-aa55-9e746d9e01aa

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_pow_of_fg

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfinite : FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I))
    (s : Nat) :
    FiniteDimensional Complex (MvPolynomial (Fin (m + 1)) Complex ⧸ I ^ s) := by
  apply OAI.PiExponent.FormalInterpolation.finiteDimensional_quotient_pow_of_fg
  exact Ideal.fg_of_isNoetherianRing I
  exact hfinite