-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_algebraMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:46:07.17498+00:00
-- url     : https://prove2.me/submissions/ababb93f-a454-4a26-b5bf-0dc354268a6d

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

theorem solution
    {R : Type*} [CommRing R] [Algebra ℂ R] (I : Ideal R)
    [Module R (R ⧸ I)] [Module ℂ (R ⧸ I)]
    [IsScalarTower ℂ R (R ⧸ I)] (c : ℂ) (p : R) :
    Ideal.Quotient.mk I (algebraMap ℂ R c * p) =
      c • Ideal.Quotient.mk I p := by
  rw [← Algebra.smul_def]
  rfl
