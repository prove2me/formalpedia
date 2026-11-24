-- Prove2me | solution 3 for Kyprianou.Ch03.stableFracMomentNegativePowerTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:49:58.896777+00:00
-- url     : https://prove2.me/submissions/27ec14da-65d0-42bf-a6e1-14c6f2fb01a1

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositivePowerTailV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (c alpha eta : Real) :
    IntegrableOn (fun x : Real => c * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume ↔ c = 0 ∨ eta < alpha := by
  let f : ℝ → ℝ := fun x => c * x ^ (eta - 1 - alpha)
  let g : ℝ → ℝ := fun x => f (-x)
  change IntegrableOn g (Iic (-1 : ℝ)) volume ↔ _
  have h : IntegrableOn g (Iic (-1 : ℝ)) volume ↔
      IntegrableOn f (Ici (1 : ℝ)) volume := by
    constructor
    · intro hg
      have hh := IntegrableOn.comp_neg_Ici (G := ℝ) (F := ℝ)
        (μ := volume) (c := (1 : ℝ)) (f := g) hg
      simpa only [g, neg_neg] using hh
    · intro hf
      have hf' : IntegrableOn f (Ici (-(-1 : ℝ))) volume := by
        simpa only [neg_neg] using hf
      exact IntegrableOn.comp_neg_Iic (G := ℝ) (F := ℝ)
        (μ := volume) (c := (-1 : ℝ)) (f := f) hf'
  exact h.trans (Kyprianou.Ch03.stableFracMomentPositivePowerTailV1 c alpha eta)
