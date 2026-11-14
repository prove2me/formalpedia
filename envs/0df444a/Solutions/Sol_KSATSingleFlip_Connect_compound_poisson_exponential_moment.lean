-- Prove2me | solution 1 for KSATSingleFlip.Connect.compound_poisson_exponential_moment
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:51:28.569899+00:00
-- url     : https://prove2.me/submissions/f03a8e12-7808-4c16-88bd-70442c0251b1

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Theorems.Thm_KSATSingleFlip_Connect_exponential_convolution_moment
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ)
    (hmom : (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) ≠ ∞) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂(compoundPoisson μ)) =
      ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal) *
        Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ).toReal)) := by
  have hfin : μ Set.univ ≠ ∞ := measure_ne_top μ _
  let I : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ
  let M : ℝ := (μ Set.univ).toReal
  let r : ℝ := I.toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hrI : ENNReal.ofReal r = I := ENNReal.ofReal_toReal hmom
  have hf : ∀ j : ℕ, IsFiniteMeasure (convPow μ j) := by
    intro j
    induction j with
    | zero => simp [convPow]; infer_instance
    | succ j ih => letI := ih; change IsFiniteMeasure (μ ∗ convPow μ j); infer_instance
  have hp (j : ℕ) : (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂(convPow μ j)) = I^j := by
    induction j with
    | zero => simp [convPow, lintegral_dirac]
    | succ j ih =>
      letI := hf j
      change (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂(μ ∗ convPow μ j)) = I^(j+1)
      rw [exponential_convolution_moment, ih, pow_succ]
      exact mul_comm _ _
  have hsumR : HasSum (fun j : ℕ => Real.exp (-M)*(r^j/(j.factorial:ℝ)))
      (Real.exp (-M)*Real.exp r) := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp r).mul_left (Real.exp (-M))
  have hsum : (∑' j : ℕ, ENNReal.ofReal (Real.exp (-M)*(r^j/(j.factorial:ℝ)))) =
      ENNReal.ofReal (Real.exp (-M)*Real.exp r) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumR.summable, hsumR.tsum_eq]
  unfold compoundPoisson
  rw [if_neg hfin, lintegral_sum_measure]
  simp_rw [lintegral_smul_measure, smul_eq_mul, hp]
  have heq (j : ℕ) : ENNReal.ofReal (Real.exp (-M)/(j.factorial:ℝ))*I^j =
      ENNReal.ofReal (Real.exp (-M)*(r^j/(j.factorial:ℝ))) := by
    rw [← hrI, ← ENNReal.ofReal_pow hr]
    rw [← ENNReal.ofReal_mul (show 0 ≤ Real.exp (-M)/(j.factorial:ℝ) by positivity)]
    congr 1
    ring
  change (∑' j : ℕ, ENNReal.ofReal (Real.exp (-M)/(j.factorial:ℝ))*I^j) = _
  simp_rw [heq]
  exact hsum
