-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawComplexLaplaceAnalyticV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:57:13.412308+00:00
-- url     : https://prove2.me/submissions/56def8a9-c4ac-41f9-929d-85faa1721e3e

import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceDifferentiableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceContinuousClosedV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceNormBoundV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    DiffContOnCl ℂ (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q)
      {z : ℂ | 0 < z.re} ∧
    ∀ z : ℂ, 0 ≤ z.re → ‖∫ x, Complex.exp (-z * (x : ℂ)) ∂Q‖ ≤ 1 := by
  refine ⟨⟨Kyprianou.Ch02.nonnegativeLawLaplaceDifferentiableV1 Q hQ, ?_⟩, Kyprianou.Ch02.nonnegativeLawLaplaceNormBoundV1 Q hQ⟩
  rw [Complex.closure_setOfPred_lt_re]
  exact Kyprianou.Ch02.nonnegativeLawLaplaceContinuousClosedV1 Q hQ
