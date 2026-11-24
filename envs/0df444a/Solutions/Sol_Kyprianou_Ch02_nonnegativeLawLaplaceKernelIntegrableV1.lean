-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawLaplaceKernelIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:33.643566+00:00
-- url     : https://prove2.me/submissions/daaf82a4-11e6-4d7f-9f89-736ea0595b43

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun x : ℝ => Complex.exp (-z * (x : ℂ))) Q := by
  have hpos : ∀ᵐ x ∂Q, 0 ≤ x := by
    rw [ae_iff]
    change Q {x : ℝ | ¬ 0 ≤ x} = 0
    have he : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by ext x; simp [not_le]
    rw [he, hQ]
  apply (integrable_const (1 : ℝ)).mono'
  · exact (show Continuous (fun x : ℝ => Complex.exp (-z * (x : ℂ))) by fun_prop).aestronglyMeasurable
  · exact hpos.mono fun x hx => Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z hz x hx
