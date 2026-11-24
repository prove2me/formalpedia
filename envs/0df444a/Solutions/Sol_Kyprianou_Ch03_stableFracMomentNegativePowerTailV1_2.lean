-- Prove2me | solution 2 for Kyprianou.Ch03.stableFracMomentNegativePowerTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:44:28.577267+00:00
-- url     : https://prove2.me/submissions/be53d660-5bea-467f-b71d-15bc1977215a

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositivePowerTailV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by
  let f : ℝ → ℝ := fun x => c*x^(eta-1-alpha)
  have hh : IntegrableOn (fun x : ℝ => f (-x)) (Iic (-1 : ℝ)) volume ↔
      IntegrableOn f (Ici (1 : ℝ)) volume := by
    constructor
    · intro h
      have h' : IntegrableOn (fun x : ℝ => f (-x)) (Iic (-(1 : ℝ))) volume := h
      have h'' : IntegrableOn (fun x : ℝ => f (-(-x))) (Ici (1 : ℝ)) volume :=
        IntegrableOn.comp_neg_Ici (c := (1 : ℝ)) h'
      simpa only [neg_neg] using h''
    · intro h
      have h' : IntegrableOn f (Ici (-(-1 : ℝ))) volume := by simpa only [neg_neg] using h
      exact IntegrableOn.comp_neg_Iic (c := (-1 : ℝ)) h'
  exact hh.trans (Kyprianou.Ch03.stableFracMomentPositivePowerTailV1 c alpha eta)
