-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLaplaceIntegralDifferentiableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:40.459932+00:00
-- url     : https://prove2.me/submissions/edd5fdca-0bc4-4555-b544-3bd9f8b54277

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceAffineIntegralDifferentiableV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Theorems.Thm_Kyprianou_Ch02_positiveComplexLaplaceKernelIntegrableV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|)
      (ν.restrict (Set.Ioi (0 : ℝ)))) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (1 - Complex.exp (-z * (x : ℂ))) ∂ν) {z : ℂ | 0 < z.re} := by
  have hpos : ∀ᵐ x ∂ν.restrict (Set.Ioi (0 : ℝ)), 0 ≤ x :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx => le_of_lt hx
  have hi (z : ℂ) (hz : 0 < z.re) :
      Integrable (fun x : ℝ => (1 : ℂ) + (-1 : ℂ) * Complex.exp (-z * (x : ℂ)))
        (ν.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [sub_eq_add_neg] using
      Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1 ν hint z hz.le
  simpa [sub_eq_add_neg] using
    Kyprianou.Ch02.complexLaplaceAffineIntegralDifferentiableV1
      (ν.restrict (Set.Ioi (0 : ℝ))) hpos hint 1 (-1) hi
