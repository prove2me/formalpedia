-- Prove2me | solution 1 for Helfgott.actual_mellin_strip_decay_expanded
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:01:41.523988+00:00
-- url     : https://prove2.me/submissions/8a3157bf-cc1b-45af-bcb7-0b70ebd01813

import Theorems.Thm_Helfgott_actual_mellin_strip_decay_complete
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set


open Helfgott
theorem solution (η : ℝ → ℝ)
    (hη : η = Helfgott.etaPlus ∨ η = Helfgott.etaStar) (n : ℕ) (a b W : ℝ) (ha : -1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ δ t : ℝ, a ≤ σ → σ ≤ b → abs δ ≤ W →
      ((1 : ℝ) + (abs t)^n) * norm (mellin
        (fun u : ℝ => (η u : ℂ) * Complex.exp
          (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) * (u : ℂ)))
        ((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C := actual_mellin_strip_decay_complete η hη n a b W ha
#print axioms solution
