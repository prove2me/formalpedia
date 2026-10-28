-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_trdeg_lt_aleph0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:32:03.245014+00:00
-- url     : https://prove2.me/submissions/d7af829c-c597-445e-a854-d9812a489b20

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem solution {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] : Algebra.trdeg Complex (MvPolynomial (Fin (Nat.succ m)) Complex ⧸ P) < Cardinal.aleph0 := by
  have h1 := trdeg_le_of_surjective (Ideal.Quotient.mkₐ Complex P)
    (Ideal.Quotient.mkₐ_surjective Complex P)
  rw [MvPolynomial.trdeg_of_isDomain] at h1
  exact h1.trans_lt (by simpa using Cardinal.natCast_lt_aleph0 (n := m + 1))
