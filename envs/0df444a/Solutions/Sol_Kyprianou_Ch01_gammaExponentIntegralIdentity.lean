-- Prove2me | solution 1 for Kyprianou.Ch01.gammaExponentIntegralIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:11:04.862274+00:00
-- url     : https://prove2.me/submissions/abaf9a57-4b62-417a-a1c6-c03da356b963

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_gammaFrullaniIntegrable
import Theorems.Thm_Kyprianou_Ch01_gammaFrullaniExactIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

/-- The gamma Lévy exponent integral from Chapter 1, as a proved Frullani corollary. -/
theorem solution
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (θ : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ) * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ) * (x : ℂ))) *
        ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))) =
      (β : ℂ) * Complex.log
        (1 - Complex.I * (θ : ℂ) / (α : ℂ)) := by
  have hz : (Complex.I * (θ : ℂ)).re ≤ 0 := by simp
  exact ⟨Kyprianou.Ch01.gammaFrullaniIntegrable α β
    (Complex.I * (θ : ℂ)) hα hβ hz,
    Kyprianou.Ch01.gammaFrullaniExactIntegral α β
      (Complex.I * (θ : ℂ)) hα hβ hz⟩

