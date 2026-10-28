-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ambient_le_coordinateNormalColumn_diff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:49:52.585448+00:00
-- url     : https://prove2.me/submissions/278fa203-684e-45a6-a57b-f839c6f256f5

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumnAtPrime_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_height_add_fractionField_differential_finrank

open scoped BigOperators

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
          (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) := by
  have h₁ :=
    OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime_finrank_eq_height P
  have h₂ :=
    OAI.PiExponent.FormalInterpolation.height_add_fractionField_differential_finrank P
  rw [h₁]
  exact h₂.ge