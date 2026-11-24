-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawLaplaceDifferentiableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:44.9623+00:00
-- url     : https://prove2.me/submissions/699d15fb-f32b-490a-a373-2401bb30a124

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineIntegralDifferentiableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceMinIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegativeLawLaplaceKernelIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x, Complex.exp (-z * (x : ℂ)) ∂Q) {z : ℂ | 0 < z.re} := by
  have hpos : ∀ᵐ x ∂Q, 0 ≤ x := by
    rw [ae_iff]
    have he : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by ext x; simp [not_le]
    rw [he, hQ]
  have hi (z : ℂ) (hz : 0 < z.re) :
      Integrable (fun x : ℝ => (0 : ℂ) + (1 : ℂ) * Complex.exp (-z * (x : ℂ))) Q := by
    simpa using Kyprianou.Ch02.nonnegativeLawLaplaceKernelIntegrableV1 Q hQ z hz.le
  simpa using Kyprianou.Ch02.complexLaplaceAffineIntegralDifferentiableV1 Q hpos
    (Kyprianou.Ch02.nonnegativeLawLaplaceMinIntegrableV1 Q) 0 1 hi
