-- Prove2me | solution 1 for Kyprianou.Ch05.potentialLaplaceNormalizedExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:39:49.907205+00:00
-- url     : https://prove2.me/submissions/2ef8719a-d327-4d2f-9904-12c98054e872

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exact potential transform divided by the reciprocal regular variation factor. -/
theorem solution
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (hp : ∀ t : Real, 0 < t → 0 < Phi t)
    (hL : ∀ x : Real, 0 < x → Phi (1/x) = x^(-rho)/L x)
    (hLap : ∀ t : Real, 0 < t → positiveLaplace U t = (ENNReal.ofReal (Phi t))⁻¹)
    (t : Real) (ht : 0 < t) :
    (positiveLaplace U t).toReal / (t^(-rho)*L (1/t)) = 1 := by
  have hf := hL (1/t) (one_div_pos.mpr ht)
  rw [one_div,one_div,inv_inv,Real.inv_rpow ht.le,Real.rpow_neg ht.le,inv_inv] at hf
  rw [hLap t ht,ENNReal.toReal_inv,ENNReal.toReal_ofReal (hp t ht).le]
  have hL0 : L t⁻¹ ≠ 0 := by
    intro h
    rw [h,div_zero] at hf
    exact (ne_of_gt (hp t ht)) hf
  rw [one_div,Real.rpow_neg ht.le,hf]
  field_simp [hL0,ne_of_gt (Real.rpow_pos_of_pos ht rho)]
