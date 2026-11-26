-- Prove2me | solution 1 for Kyprianou.Ch05.markedPositiveCrossingKernelIntegrateV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:23:44.105884+00:00
-- url     : https://prove2.me/submissions/c85b574b-c789-447b-abe1-03610b523e5f

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    (Pi : Measure ℝ) (eta x s v : ℝ) (A B : Set ℝ) :
    (∫⁻ z, if 0 < s ∧ v ∈ Icc (0 : ℝ) x ∧ x-v < z ∧
      z-(x-v) ∈ A ∧ x-v ∈ B then ENNReal.ofReal (Real.exp (-eta*s)) else 0 ∂Pi) =
    if 0 < s then ENNReal.ofReal (Real.exp (-eta*s)) * (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0) v else 0 := by
  classical
  by_cases ht : 0 < s
  · by_cases hv : v ∈ Icc (0 : ℝ) x
    · simp only [ht,hv,true_and,if_true]
      rw [← lintegral_indicator measurableSet_Ioi,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      by_cases hz : x-v < z
      · by_cases hm : z-(x-v) ∈ A ∧ x-v ∈ B <;>
          simp [Set.indicator,hz,hm]
      · simp [Set.indicator,hz]
    · simp [ht,hv]
  · simp [ht]
