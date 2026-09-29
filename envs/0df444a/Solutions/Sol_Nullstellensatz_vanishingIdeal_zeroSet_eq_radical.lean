-- Prove2me | solution 1 for Nullstellensatz.vanishingIdeal_zeroSet_eq_radical
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T22:17:00.503345+00:00
-- url     : https://prove2.me/submissions/ce731dd1-4795-4d35-af3b-8796f612ab22

import Definitions.Def_Nullstellensatz_Defs
import Mathlib

open MvPolynomial

theorem solution {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) K)) :
    Nullstellensatz.vanishingIdeal (Nullstellensatz.zeroSet J) = J.radical := by
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K) J]
  ext p
  simp only [MvPolynomial.mem_vanishingIdeal_iff, MvPolynomial.mem_zeroLocus_iff,
    MvPolynomial.coe_aeval_eq_eval]
  rfl
