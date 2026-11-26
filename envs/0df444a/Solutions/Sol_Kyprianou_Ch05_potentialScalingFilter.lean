-- Prove2me | solution 1 for Kyprianou.Ch05.potentialScalingFilter
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:39:56.049334+00:00
-- url     : https://prove2.me/submissions/37beee49-d49d-41ac-9b52-f8f067435d82

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Karamata potential scaling at a general positive endpoint filter. -/
theorem solution
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (l : Filter Real) (hRho : 0 ≤ rho)
    (hpos : ∀ᶠ x in l, 0 < x)
    (hL : ∀ x : Real, 0 < x → 0 < L x)
    (hPhi : ∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x)
    (hCum : Tendsto (fun x : Real => (U (Icc 0 x)).toReal /
      (x^rho*L x/Real.Gamma (1+rho))) l (nhds 1))
    (a : Real) (ha : 0 < a)
    (hScale : Tendsto (fun x : Real => a*x) l l)
    (hSlow : Tendsto (fun x : Real => L (a*x)/L x) l (nhds 1)) :
    Tendsto (fun x : Real => (U (Icc 0 (a*x))).toReal*Phi (1/x)) l
      (nhds (a^rho/Real.Gamma (1+rho))) := by
  have h := ((hCum.comp hScale).mul hSlow).mul_const (a^rho/Real.Gamma (1+rho))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hpos] with x hx
  change ((U (Icc 0 (a*x))).toReal / ((a*x)^rho*L (a*x)/Real.Gamma (1+rho))) *
    (L (a*x)/L x)*(a^rho/Real.Gamma (1+rho)) = (U (Icc 0 (a*x))).toReal*Phi (1/x)
  rw [hPhi x hx,Real.mul_rpow ha.le hx.le,Real.rpow_neg hx.le]
  have hg : 0 < Real.Gamma (1+rho) := Real.Gamma_pos_of_pos (by linarith)
  field_simp [ne_of_gt (hL x hx),ne_of_gt (hL (a*x) (mul_pos ha hx)),
    ne_of_gt (Real.rpow_pos_of_pos ha rho),ne_of_gt (Real.rpow_pos_of_pos hx rho),hg.ne']
