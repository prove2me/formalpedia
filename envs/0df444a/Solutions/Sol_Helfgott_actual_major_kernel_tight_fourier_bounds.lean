-- Prove2me | solution 1 for Helfgott.actual_major_kernel_tight_fourier_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T06:22:09.1241+00:00
-- url     : https://prove2.me/submissions/48054bf4-018b-41ab-8b60-a983ac55af51

import Theorems.Thm_Helfgott_actual_major_kernel_tight_fourier_bounds_complete
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.FourierTransform
open MeasureTheory Set Complex
open scoped FourierTransform

open Helfgott
theorem solution :
    let K : ℝ → ℂ := fun u => (majorKernel (Real.exp u) : ℂ)
    Integrable (𝓕 K) ∧ (∫ u : ℝ,‖K u‖)≤5/2 ∧
      (∀ ξ : ℝ,‖𝓕 K ξ‖≤5/2) ∧
      (∀ ξ : ℝ,ξ^2*‖𝓕 K ξ‖≤5/12) ∧
      (∫ ξ : ℝ,‖𝓕 K ξ‖)≤25/6 := actual_major_kernel_tight_fourier_bounds_complete
#print axioms solution
