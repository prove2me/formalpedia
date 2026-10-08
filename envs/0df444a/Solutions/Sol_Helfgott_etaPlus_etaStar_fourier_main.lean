-- Prove2me | solution 1 for Helfgott.etaPlus_etaStar_fourier_main
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:02:26.384174+00:00
-- url     : https://prove2.me/submissions/a249eaab-2a6e-4c03-9122-9fa83d8c2b4c

import Theorems.Thm_Helfgott_etaPlus_etaStar_fourier_main_explicit
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
open scoped FourierTransform
open Helfgott
theorem solution (ρ : ℝ) : Integrable (fun ξ : ℝ => (𝓕 (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
      𝓕 (fun t : ℝ => (etaStar t : ℂ)) ξ) ∧
    (∫ ξ : ℝ,(Real.fourierChar (ρ*ξ) : ℂ)*
      (𝓕 (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
      𝓕 (fun t : ℝ => (etaStar t : ℂ)) ξ) =
      (((∫ w in Ioi (0 : ℝ),etaStar w*
        (∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))) : ℝ) : ℂ) := etaPlus_etaStar_fourier_main_explicit ρ
#print axioms solution
