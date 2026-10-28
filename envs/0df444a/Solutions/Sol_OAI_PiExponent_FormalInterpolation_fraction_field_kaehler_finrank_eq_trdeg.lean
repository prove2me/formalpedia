-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fraction_field_kaehler_finrank_eq_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:46:47.715118+00:00
-- url     : https://prove2.me/submissions/6d8f3bae-3b5e-4c13-8782-c7aa762cc699

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_kaehler_finrank_eq_trdeg_of_finite
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fraction_field_finite_trdeg

open scoped KaehlerDifferential
open OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (logarithmicPrimeField P) (Ω[logarithmicPrimeField P⁄Complex]) =
    (Algebra.trdeg Complex (logarithmicPrimeField P)).toNat := by
  apply kaehler_finrank_eq_trdeg_of_finite
  exact fraction_field_finite_trdeg P