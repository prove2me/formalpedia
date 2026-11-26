-- Prove2me | solution 1 for Kyprianou.Ch05.jumpPotentialKernelMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:17:39.022243+00:00
-- url     : https://prove2.me/submissions/4f02269c-5298-42ab-b0fd-bbcfca4c9405

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_jumpPotentialInnerKernelMeasurableV1
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
    (U Pi : Measure ℝ) [SigmaFinite Pi]
    (x : ℝ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let f := (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0)
    Measurable f ∧ jumpPotentialKernel U Pi x A B = ∫⁻ v, f v ∂U := by
  classical
  let k : ℝ → ENNReal := fun v => ∫⁻ z in Ioi (x-v),
    if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
  dsimp only
  have he : (fun v : ℝ => if v ∈ Icc (0 : ℝ) x then
      ∫⁻ z in Ioi (x-v), if z-(x-v) ∈ A ∧ x-v ∈ B then (1 : ENNReal) else 0 ∂Pi
      else 0) = (Icc (0 : ℝ) x).indicator k := by
    funext v
    simp only [Set.indicator,k]
  rw [he]
  refine ⟨(jumpPotentialInnerKernelMeasurableV1 Pi x A B hA hB).indicator measurableSet_Icc,?_⟩
  rw [lintegral_indicator measurableSet_Icc]
  rfl
