-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentNegativePowerTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:43:11.805163+00:00
-- url     : https://prove2.me/submissions/67c675ec-e494-4b3e-a85d-60a914c118e8

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositivePowerTailV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by
  have h : IntegrableOn (fun x : ℝ => c*(-x)^(eta-1-alpha)) (Iic (-1 : ℝ)) volume ↔
      IntegrableOn (fun x : ℝ => c*x^(eta-1-alpha)) (Ici (1 : ℝ)) volume := by
    constructor
    · intro h
      have hh := IntegrableOn.comp_neg_Ici (G := ℝ) (F := ℝ)
        (μ := volume) (c := (1 : ℝ))
        (f := fun y : ℝ => c * (-y) ^ (eta - 1 - alpha)) h
      simpa only [neg_neg] using hh
    · intro h
      exact IntegrableOn.comp_neg_Iic (G := ℝ) (F := ℝ)
        (μ := volume) (c := (-1 : ℝ))
        (f := fun y : ℝ => c * y ^ (eta - 1 - alpha)) (by simpa only [neg_neg] using h)
  rw [h, Kyprianou.Ch03.stableFracMomentPositivePowerTailV1]
