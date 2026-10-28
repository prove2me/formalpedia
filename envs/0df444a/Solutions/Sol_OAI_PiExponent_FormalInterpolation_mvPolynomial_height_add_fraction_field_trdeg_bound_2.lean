-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.mvPolynomial_height_add_fraction_field_trdeg_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T07:41:10.616334+00:00
-- url     : https://prove2.me/submissions/479d4c85-e790-4fca-abe5-e7aa774fe204

import Mathlib.Data.Complex.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_eq_height
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_coordinateNormalColumn_span_finrank_add_trdeg_toNat
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    m + 1 ≤ P.height +
      (Algebra.trdeg Complex
        (FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P))).toNat := by
  rw [← coordinateNormalColumn_span_finrank_eq_height P]
  exact_mod_cast (coordinateNormalColumn_span_finrank_add_trdeg_toNat P).ge
