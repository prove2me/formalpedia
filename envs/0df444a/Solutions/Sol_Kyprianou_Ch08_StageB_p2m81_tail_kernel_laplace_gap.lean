-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:34:49.02256+00:00
-- url     : https://prove2.me/submissions/b06f220b-5a21-41e2-a8bc-d4f3818cc015

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_excess_laplace_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_f_closed_form_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_gap_point_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d)) :
    ∃ κ : Measure ℝ, SFinite κ ∧ κ (Iio (0 : ℝ)) = 0 ∧ (∀ x : ℝ, κ {x} = 0) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
          ENNReal.ofReal d * (1 - (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s) ∧
      (∀ s : ℝ, 0 < s → s ≠ d →
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂κ) =
          ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s)))) ∧
      (∃ s0 : ℝ, 0 < s0 ∧
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s0 * y)) ∂κ) < 1) := by
  haveI := hprob
  refine ⟨volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  · rw [withDensity_apply _ measurableSet_Iio]
    exact setLIntegral_eq_zero measurableSet_Iio (fun y hy => if_neg (not_le_of_gt (mem_Iio.mp hy)))
  · intro x
    rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton, Real.volume_singleton, mul_zero]
  · exact fun s hs => Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public d ρ hprob hsupp s hs
  · exact fun s hs hne => Kyprianou.Ch08.StageB.p2m81_tail_kernel_f_closed_form_public f hpos d hd ρ hprob hsupp heq s hs hne
  · exact Kyprianou.Ch08.StageB.p2m81_tail_kernel_gap_point_public d hd ρ hprob hsupp
