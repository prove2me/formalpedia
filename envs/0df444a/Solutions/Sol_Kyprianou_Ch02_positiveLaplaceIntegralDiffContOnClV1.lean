-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLaplaceIntegralDiffContOnClV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:57:18.193666+00:00
-- url     : https://prove2.me/submissions/3131e170-17ab-40dc-a0f9-62d0a8f37fa9

import Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralDifferentiableV1
import Theorems.Thm_Kyprianou_Ch02_positiveLaplaceIntegralContinuousClosedV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_positiveComplexLaplaceKernelIntegrableV1
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    DiffContOnCl ℂ (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 < z.re} := by
  refine ⟨Kyprianou.Ch02.positiveLaplaceIntegralDifferentiableV1 ν hint, ?_⟩
  rw [Complex.closure_setOfPred_lt_re]
  exact Kyprianou.Ch02.positiveLaplaceIntegralContinuousClosedV1 ν hint
