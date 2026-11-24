-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegativeLawLaplaceNormBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:00:53.668243+00:00
-- url     : https://prove2.me/submissions/09ff55a9-dd6a-4e7a-bde1-66afb6d37cd3

import Theorems.Thm_Kyprianou_Ch02_complexLaplaceKernelNormLeOneV1
import Theorems.Thm_Kyprianou_Ch02_complexLaplaceDerivativeUniformBoundV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hQ : Q (Set.Iio (0 : ℝ)) = 0) :
    ∀ z : ℂ, 0 ≤ z.re → ‖∫ x, Complex.exp (-z * (x : ℂ)) ∂Q‖ ≤ 1 := by
  have hpos : ∀ᵐ x ∂Q, 0 ≤ x := by
    rw [ae_iff]
    have he : {x : ℝ | ¬ 0 ≤ x} = Set.Iio 0 := by ext x; simp [not_le]
    rw [he, hQ]
  let F (z : ℂ) (x : ℝ) : ℂ := Complex.exp (-z * (x : ℂ))
  let F' (z : ℂ) (x : ℝ) : ℂ := -(x : ℂ) * F z x
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) Q :=
    (show Continuous (F z) by dsimp [F]; fun_prop).aestronglyMeasurable
  have hnorm (z : ℂ) (hz : 0 ≤ z.re) : ∀ᵐ x ∂Q, ‖F z x‖ ≤ 1 :=
    hpos.mono fun x hx => Kyprianou.Ch02.complexLaplaceKernelNormLeOneV1 z hz x hx
  intro z hz
  simpa [F] using norm_integral_le_of_norm_le_const (hnorm z hz)
