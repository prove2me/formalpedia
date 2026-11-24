-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLaplaceIntegralRealNonnegV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:53:25.615563+00:00
-- url     : https://prove2.me/submissions/05a4cb38-c10d-41dc-b1ed-09cd1a229b92

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
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
      (ν.restrict (Set.Ioi (0 : ℝ)))) (z : ℂ) (hz : 0 ≤ z.re) :
    0 ≤ (∫ x in Set.Ioi (0 : ℝ), (1 - Complex.exp (-z * (x : ℂ))) ∂ν).re := by
  change 0 ≤ RCLike.re (∫ x in Set.Ioi (0 : ℝ),
    (1 - Complex.exp (-z * (x : ℂ))) ∂ν)
  rw [← integral_re (Kyprianou.Ch02.positiveComplexLaplaceKernelIntegrableV1 ν hint z hz)]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hn := Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z hz x hx.le
  have hre := Complex.re_le_norm (Complex.exp (-z * (x : ℂ)))
  change 0 ≤ (1 - Complex.exp (-z * (x : ℂ))).re
  simp only [Complex.sub_re, Complex.one_re]
  linarith
