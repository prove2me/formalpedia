-- Prove2me | solution 1 for Helfgott.actual_gaussian_mellin_sharp_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T06:22:16.634837+00:00
-- url     : https://prove2.me/submissions/a3ff67b8-5914-484e-9cec-3efbb0d3f9a5

import Theorems.Thm_Helfgott_actual_gaussian_mellin_sharp_exponential_bound_complete
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set Complex

open Helfgott
theorem solution (σ ω t θ c : ℝ)
    (hσl : -(3/2 : ℝ)≤σ) (hσu : σ≤0) (hθ0 : 0≤θ) (hθ : θ≤1/4)
    (hc : (4/5 : ℝ)≤c) (hcos : c≤Real.cos (2*θ)) :
    ‖mellin (fun u : ℝ => (phi u : ℂ)*Complex.exp (I*(ω : ℂ)*(u : ℂ)))
      ((σ : ℂ)+(t : ℂ)*I)‖≤
      (5+3*|ω| *θ/c)*Real.exp (-θ*|t|+ω^2*θ^2/(2*c)) := actual_gaussian_mellin_sharp_exponential_bound_complete σ ω t θ c hσl hσu hθ0 hθ hc hcos
#print axioms solution
