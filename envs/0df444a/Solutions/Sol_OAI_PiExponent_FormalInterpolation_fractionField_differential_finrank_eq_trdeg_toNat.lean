-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg_toNat
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T01:05:19.330684+00:00
-- url     : https://prove2.me/submissions/b4404e17-2838-46a1-a546-8866f4bf85b0

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.FieldTheory.FinTrdeg
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fractionField_finiteTrdeg_of_primeMvPolynomialQuotient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_field_kaehlerDifferential_finrank_eq_trdeg_toNat

open scoped BigOperators

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) =
      (Algebra.trdeg Complex
        (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat := by
  letI : FinTrdeg Complex
      (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P) :=
    OAI.PiExponent.FormalInterpolation.fractionField_finiteTrdeg_of_primeMvPolynomialQuotient P
  exact OAI.PiExponent.FormalInterpolation.field_kaehlerDifferential_finrank_eq_trdeg_toNat
    (K := Complex)
    (L := OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)