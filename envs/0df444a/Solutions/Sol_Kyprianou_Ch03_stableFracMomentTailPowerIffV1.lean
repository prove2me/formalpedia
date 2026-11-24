-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentTailPowerIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:04:36.413836+00:00
-- url     : https://prove2.me/submissions/de86006a-d554-4166-815d-6659f321b3d7

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositiveTailWeightedV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativeTailWeightedV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentPositivePowerTailV1
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativePowerTailV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha cPlus cMinus eta : Real)
    (hAlpha : 0 < alpha ∧ alpha < 2)
    (hCPlus : 0 ≤ cPlus) (hCMinus : 0 ≤ cMinus)
    (hNonzero : 0 < cPlus + cMinus)
    (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) {x : Real | 1 ≤ |x|}
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔ eta < alpha := by
  let m := (volume : Measure ℝ).withDensity
    (fun x : ℝ => ENNReal.ofReal (if 0 < x then cPlus / (x ^ (1+alpha))
       else if x < 0 then cMinus / ((-x) ^ (1+alpha)) else 0))
  let f (x : ℝ) := (max |x| 1)^eta
  have he : {x : ℝ | 1 ≤ |x|} = Ici (1 : ℝ) ∪ Iic (-1 : ℝ) := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Ici, mem_Iic]
    constructor
    · intro h
      by_cases hx : 0 ≤ x
      · left; simpa [abs_of_nonneg hx] using h
      · right; rw [abs_of_neg (lt_of_not_ge hx)] at h; linarith
    · rintro (h | h)
      · rw [abs_of_nonneg (by linarith : 0 ≤ x)]; exact h
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
  rw [he, integrableOn_union,
    Kyprianou.Ch03.stableFracMomentPositiveTailWeightedV1 alpha cPlus cMinus eta hCPlus hCMinus hEta,
    Kyprianou.Ch03.stableFracMomentNegativeTailWeightedV1 alpha cPlus cMinus eta hCPlus hCMinus hEta,
    Kyprianou.Ch03.stableFracMomentPositivePowerTailV1,
    Kyprianou.Ch03.stableFracMomentNegativePowerTailV1]
  constructor
  · rintro ⟨hp, hm⟩
    rcases hp with hp | h
    · rcases hm with hm | h
      · linarith
      · exact h
    · exact h
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩
