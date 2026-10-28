-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fractionField_finiteTrdeg_of_primeMvPolynomialQuotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:32:18.241161+00:00
-- url     : https://prove2.me/submissions/6af3db0b-49a1-4d53-8a68-cc279b544368

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.FieldTheory.FinTrdeg

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    FinTrdeg Complex (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) := by
  apply FinTrdeg.of_trdeg
  set B := MvPolynomial (Fin (m + 1)) Complex ⧸ P
  have hB : Algebra.trdeg Complex B ≤ (m + 1 : Nat) := by
    have h1 := trdeg_le_of_surjective (Ideal.Quotient.mkₐ Complex P)
      (Ideal.Quotient.mkₐ_surjective Complex P)
    rw [MvPolynomial.trdeg_of_isDomain] at h1
    simpa using h1
  have hL : Algebra.trdeg B (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) = 0 := by
    have : Algebra.IsAlgebraic B (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors B)
    exact trdeg_eq_zero
  have hadd := trdeg_add_eq (R := Complex) (S := B)
    (A := OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
  rw [hL, add_zero] at hadd
  rw [← hadd]
  exact hB.trans_lt Cardinal.natCast_lt_aleph0
