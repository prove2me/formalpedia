-- Prove2me | solution 1 for OAI.PiExponent.laurent_derivative_residue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:27:05.444284+00:00
-- url     : https://prove2.me/submissions/9e150ab5-5e1b-4949-aa3a-b7eba82c2ad1

import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic


namespace OAI
namespace PiExponent
end PiExponent
end OAI
open scoped LaurentSeries Matrix
open OAI.PiExponent

theorem solution {K : Type*} [Field K]
    (f : K⸨X⸩) : (LaurentSeries.derivative K f).coeff (-1) = 0 := by
  simp [LaurentSeries.derivative]
