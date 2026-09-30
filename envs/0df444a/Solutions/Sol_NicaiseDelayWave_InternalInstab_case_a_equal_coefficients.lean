-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.case_a_equal_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:47:59.660985+00:00
-- url     : https://prove2.me/submissions/50aaecca-0ddc-4b6e-af23-075255b49a2a

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (μ τ α β Λ : ℝ) (hμ : 0 < μ) (hτ : 0 < τ)
    (h₁ : α ^ 2 + β ^ 2 = Λ ^ 2) (h₂ : μ * Real.exp (-α * τ) = 2 * α + μ) :
    α = 0 ∧ β ^ 2 = Λ ^ 2 := by
  have hα : α = 0 := by
    rcases lt_trichotomy α 0 with h | h | h
    · have hexp : 1 < Real.exp (-α * τ) := Real.one_lt_exp_iff.mpr (by nlinarith)
      have hmul := mul_lt_mul_of_pos_left hexp hμ
      nlinarith
    · exact h
    · have hexp : Real.exp (-α * τ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      have hmul := mul_lt_mul_of_pos_left hexp hμ
      nlinarith
  constructor
  · exact hα
  · simpa [hα] using h₁
