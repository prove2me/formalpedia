-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.height_add_fractionField_differential_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T00:59:33.059538+00:00
-- url     : https://prove2.me/submissions/873358cd-2a2f-46de-ab17-08d9d9c1e394

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Ideal.Height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_height_add_fractionField_trdeg_toNat
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fractionField_differential_finrank_eq_trdeg_toNat

open scoped BigOperators

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height.toNat +
      Module.finrank (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)
        (Ω[OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P⁄Complex]) = m + 1 := by
  rw [OAI.PiExponent.FormalInterpolation.fractionField_differential_finrank_eq_trdeg_toNat (m := m) P]
  exact OAI.PiExponent.FormalInterpolation.height_add_fractionField_trdeg_toNat (m := m) P