-- Prove2me | solution 1 for Kyprianou.Ch01.complexExpDeficitTwoNorm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:54:24.792204+00:00
-- url     : https://prove2.me/submissions/5e781883-7ce7-4cc2-b061-236f1c7bd619

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

/-- The complex exponential deficit is Lipschitz at zero throughout the left half-plane. -/
theorem solution (z : ℂ) (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  by_cases hsmall : ‖z‖ ≤ 1
  · exact Complex.norm_exp_sub_one_le hsmall
  · have hexp : ‖Complex.exp z‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hz
    calc
      ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by
        simp only [norm_one]
        linarith
      _ ≤ 2 * ‖z‖ := by
        have hlarge : 1 < ‖z‖ := lt_of_not_ge hsmall
        linarith
