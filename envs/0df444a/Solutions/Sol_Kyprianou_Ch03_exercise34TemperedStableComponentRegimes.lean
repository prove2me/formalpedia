-- Prove2me | solution 1 for Kyprianou.Ch03.exercise34TemperedStableComponentRegimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:12:34.809203+00:00
-- url     : https://prove2.me/submissions/e501cc3f-d26e-410b-ada7-0e02cdd9989a

import Mathlib
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_componentRegimes_gammaLaplace
import Theorems.Thm_Kyprianou_Ch03_componentRegimes_alphaOneEsscher
import Theorems.Thm_Kyprianou_Ch03_componentRegimes_otherAlphaEsscher
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03


theorem solution
(c gamma : ℝ) (hc : 0 < c) (hgamma : 0 < gamma) :
    (∀ q : ℝ, 0 ≤ q →
      (∫ x in Set.Ioi (0 : ℝ),
        (1 - Real.exp (-q * x)) ∂
          (temperedStablePositiveMeasure c 0 gamma)) =
        c * Real.log (1 + q / gamma)) ∧
    (temperedStablePositiveMeasure c 1 gamma).withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
      temperedStablePositiveMeasure c 1 0 ∧
    (∀ alpha : ℝ, (0 < alpha ∧ alpha < 1) ∨
        (1 < alpha ∧ alpha < 2) →
      (temperedStablePositiveMeasure c alpha gamma).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (gamma * x))) =
        temperedStablePositiveMeasure c alpha 0) := by
  exact ⟨
    Kyprianou.Ch03.componentRegimes_gammaLaplace c gamma hc hgamma,
    Kyprianou.Ch03.componentRegimes_alphaOneEsscher c gamma hc hgamma,
    Kyprianou.Ch03.componentRegimes_otherAlphaEsscher c gamma hc hgamma
  ⟩

