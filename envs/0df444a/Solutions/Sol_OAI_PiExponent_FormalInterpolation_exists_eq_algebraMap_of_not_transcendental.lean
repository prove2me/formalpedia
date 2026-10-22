-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_eq_algebraMap_of_not_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:26:37.364345+00:00
-- url     : https://prove2.me/submissions/78f81de7-2642-4c16-98eb-d1125f82afd6

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

open Polynomial

theorem solution
    {E : Type} [Field E] [Algebra Complex E]
    (f : E) (hf : ¬Transcendental Complex f) :
    ∃ b : Complex, algebraMap Complex E b = f := by
  have halg : IsAlgebraic Complex f := by
    simpa [Transcendental] using hf
  have hint : IsIntegral Complex f := (isAlgebraic_iff_isIntegral (K := Complex)).1 halg
  have hdeg : (minpoly Complex f).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible Complex (minpoly.irreducible hint)
  exact (minpoly.degree_eq_one_iff (A := Complex)).1 hdeg
