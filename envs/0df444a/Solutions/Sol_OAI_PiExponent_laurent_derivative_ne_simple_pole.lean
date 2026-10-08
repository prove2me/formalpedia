-- Prove2me | solution 1 for OAI.PiExponent.laurent_derivative_ne_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:28:48.399776+00:00
-- url     : https://prove2.me/submissions/e29afc4b-02f3-4dad-8d59-12493a644510

import Theorems.Thm_OAI_PiExponent_laurent_derivative_residue_eq_zero
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
    (f : K⸨X⸩) {c : K} (hc : c ≠ 0) :
    LaurentSeries.derivative K f ≠ HahnSeries.single (-1) c := by
  intro h
  have hr := congrArg (fun z : K⸨X⸩ => z.coeff (-1)) h
  exact hc (by simpa [laurent_derivative_residue_eq_zero] using hr.symm)
