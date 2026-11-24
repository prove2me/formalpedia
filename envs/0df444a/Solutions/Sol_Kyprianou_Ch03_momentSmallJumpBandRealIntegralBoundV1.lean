-- Prove2me | solution 1 for Kyprianou.Ch03.momentSmallJumpBandRealIntegralBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:05:09.346051+00:00
-- url     : https://prove2.me/submissions/9e69834c-6f16-40cd-be4a-91a4831a105b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch03_momentSmallJumpKernelIntegrableV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (e b : Real) :
    (∫ x in {x : Real | e ≤ |x| ∧ |x| < 1},
      (Real.exp (b*x)-1-b*x) ∂T.levyMeasure) ≤
    ∫ x in Set.Ioo (-1 : Real) 1, (Real.exp (b*x)-1-b*x) ∂T.levyMeasure := by
  apply integral_mono_measure
  · apply Measure.restrict_mono
    · intro x hx
      exact abs_lt.mp hx.2
    · exact le_rfl
  · filter_upwards [] with x
    change 0 ≤ Real.exp (b*x) - 1 - b*x
    linarith [Real.add_one_le_exp (b*x)]
  · exact Kyprianou.Ch03.momentSmallJumpKernelIntegrableV1 T b
