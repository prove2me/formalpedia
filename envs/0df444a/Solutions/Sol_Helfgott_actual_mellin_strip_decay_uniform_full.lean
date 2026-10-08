-- Prove2me | solution 1 for Helfgott.actual_mellin_strip_decay_uniform_full
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:01:33.649881+00:00
-- url     : https://prove2.me/submissions/1fb01b14-559c-4702-8b68-c6e0d667d31e

import Theorems.Thm_Helfgott_actual_mellin_strip_decay_complete
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform

open Helfgott
theorem solution :
    ∀ (eta : Real → Real),
    (eta = Helfgott.etaPlus ∨ eta = Helfgott.etaStar) →
    ∀ (n : Nat) (a : Real) (b : Real) (W : Real), (-1 : Real) < a →
    ∃ (C : Real), 0 ≤ C ∧
      ∀ (sigma : Real) (delta : Real) (t : Real),
        a ≤ sigma → sigma ≤ b → abs delta ≤ W →
        ((1 : Real) + (abs t)^n) * norm (mellin
          (fun u : Real => (eta u : Complex) * Complex.exp
            (Complex.I * ((2 * Real.pi * delta : Real) : Complex) * (u : Complex)))
          ((sigma : Complex) + (t : Complex) * Complex.I)) ≤ C := by
  intro eta heta n a b W ha
  exact actual_mellin_strip_decay_complete eta heta n a b W ha
#print axioms solution
