-- Prove2me | solution 1 for KSATSingleFlip.Connect.symmetric_compound_exponential_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.477807+00:00
-- url     : https://prove2.me/submissions/fbadb5e8-df5d-4a4f-8b46-abf407728097

import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_exponential_moment
import Theorems.Thm_KSATSingleFlip_Connect_exponential_convolution_moment
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ)
    (hp : (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) ≠ ∞)
    (hm : (∫⁻ x, ENNReal.ofReal (Real.exp ((-c)*x)) ∂μ) ≠ ∞) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (c*z)) ∂(compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ))) =
      ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal) * Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ).toReal) *
        (Real.exp (-(μ Set.univ).toReal) * Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp ((-c)*x)) ∂μ).toReal))) := by
  let P := compoundPoisson μ
  letI : IsProbabilityMeasure P := ⟨compound_poisson_probability μ⟩
  have hneg : (∫⁻ z, ENNReal.ofReal (Real.exp (c*z)) ∂(Measure.map (fun z : ℝ => -z) P)) =
      (∫⁻ z, ENNReal.ofReal (Real.exp ((-c)*z)) ∂P) := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    congr 2
    ring
  rw [exponential_convolution_moment, hneg]
  rw [compound_poisson_exponential_moment μ c hp, compound_poisson_exponential_moment μ (-c) hm]
  rw [← ENNReal.ofReal_mul (by positivity)]
