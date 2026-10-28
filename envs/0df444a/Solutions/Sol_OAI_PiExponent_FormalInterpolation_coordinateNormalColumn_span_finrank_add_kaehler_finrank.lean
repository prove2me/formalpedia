-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_span_finrank_add_kaehler_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:44:30.042364+00:00
-- url     : https://prove2.me/submissions/ee81a73e-f2f0-4f49-8a53-96dc1fc24c2d

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_diff_le_ambient
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ambient_le_coordinateNormalColumn_diff
import Mathlib.RingTheory.Extension.Cotangent.Basic

open scoped BigOperators

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
      (Submodule.span (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Set.range (OAI.PiExponent.FormalInterpolation.coordinateNormalColumnAtPrime P))) +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) = m + 1 := by
  apply Nat.le_antisymm
  · exact OAI.PiExponent.FormalInterpolation.coordinateNormalColumn_diff_le_ambient P
  · exact OAI.PiExponent.FormalInterpolation.ambient_le_coordinateNormalColumn_diff P