-- Prove2me | solution 1 for Helfgott.etaPlus_etaStar_fourier_truncation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T07:02:33.414344+00:00
-- url     : https://prove2.me/submissions/d668f471-84d9-406f-92a9-57304ae5344f

import Theorems.Thm_Helfgott_etaPlus_etaStar_fourier_truncation_explicit
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set
open scoped FourierTransform
open Helfgott
theorem solution (ρ R : ℝ) (hR : 0 < R) : ‖(((∫ w in Ioi (0:ℝ),etaStar w*(∫ u : ℝ,etaPlus u*etaPlus (ρ-w-u))) : ℝ) : ℂ)-
      (∫ ξ in Icc (-R) R,(Real.fourierChar (ρ*ξ) : ℂ)*
        (𝓕 (fun t : ℝ => (etaPlus t : ℂ)) ξ)^2*
        𝓕 (fun t : ℝ => (etaStar t : ℂ)) ξ)‖ ≤ 591/R^3 := etaPlus_etaStar_fourier_truncation_explicit ρ R hR
#print axioms solution
