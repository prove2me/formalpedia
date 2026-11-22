-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:48:13.189797+00:00
-- url     : https://prove2.me/submissions/3c0b0caa-69ff-462d-b2f9-ad16c785ccef

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_withdensity_to_iterated_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_swap_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_inner_exp_lintegral_public
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_laplace_tsub_public
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℝ) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s := by
  have h1 := Kyprianou.Ch08.StageB.p2m81_tail_kernel_withdensity_to_iterated_public d ρ s
  have h2 := Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_swap_public s ρ hprob
  have h_to_gap : (∫⁻ z : ℝ, (∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume) ∂ρ) =
      (∫⁻ z : ℝ, (1 - ENNReal.ofReal (Real.exp (-s * z))) / ENNReal.ofReal s ∂ρ) := by
    apply lintegral_congr
    intro z
    exact Kyprianou.Ch08.StageB.p2m81_tail_kernel_inner_exp_lintegral_public s hs z
  have hH_meas2 : Measurable (fun z : ℝ => 1 - ENNReal.ofReal (Real.exp (-s * z))) := by fun_prop
  have h_div : (∫⁻ z : ℝ, (1 - ENNReal.ofReal (Real.exp (-s * z))) / ENNReal.ofReal s ∂ρ) =
      (∫⁻ z : ℝ, (1 - ENNReal.ofReal (Real.exp (-s * z))) ∂ρ) / ENNReal.ofReal s := by
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const _ hH_meas2]
  have h_tsub := Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_tsub_public s hs ρ hprob hsupp
  rw [h1, h2, h_to_gap, h_div, h_tsub]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
