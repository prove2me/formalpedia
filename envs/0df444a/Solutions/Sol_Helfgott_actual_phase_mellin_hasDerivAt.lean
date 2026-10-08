-- Prove2me | solution 1 for Helfgott.actual_phase_mellin_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:02:02.524155+00:00
-- url     : https://prove2.me/submissions/817d3c7f-59c8-4795-8ab7-a6aafb4b25c7

import Theorems.Thm_Helfgott_actual_phase_mellin_derivative_explicit
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set


open Helfgott
theorem solution (η : ℝ → ℝ) (hη : η=Helfgott.etaPlus ∨ η=Helfgott.etaStar)
    (ω : ℝ) (s : ℂ) (hs : -1 < s.re) :
    let f : ℝ → ℂ := fun t => (η t : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))
    MellinConvergent (fun t : ℝ => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t : ℝ => Real.log t • f t) s) s := actual_phase_mellin_derivative_explicit η hη ω s hs
#print axioms solution
