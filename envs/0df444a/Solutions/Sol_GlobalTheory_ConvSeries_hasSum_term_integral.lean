-- Prove2me | solution 1 for GlobalTheory.ConvSeries.hasSum_term_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:02.909598+00:00
-- url     : https://prove2.me/submissions/223ce196-b148-43b8-9bdf-ec81735bc923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
import Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_norm_wt_le
import Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_continuous_wt
import Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_integrable_gauss
import Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_coef_apply_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ConvSeries
open GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
namespace GlobalTheory.ConvSeries
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h : SchwartzMap E ℂ) (y : E) :
    HasSum (fun k => term b c h k y)
      (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) := by
  set z : E → ℂ := fun a => ((2 * c * inner ℝ a y : ℝ) : ℂ) with hz
  have hzc : Continuous z := by rw [hz]; fun_prop
  let F : ℕ → E → ℂ := fun n a => wt b c h a * (z a ^ n / (n.factorial : ℂ))
  have hF : ∀ n, (∫ a, F n a) =
      (((2 * c) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) * coef b c h n (fun _ => y) := by
    intro n
    rw [coef_apply_const hb hc h n y, ← integral_const_mul]
    congr 1; funext a
    simp only [F, z]; push_cast; ring
  have hsum : HasSum (fun n => ∫ a, F n a) (∫ a, wt b c h a * Complex.exp (z a)) := by
    refine hasSum_integral_of_dominated_convergence
      (fun n a => ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) ?_ ?_ ?_ ?_ ?_
    · intro n
      have := continuous_wt b c h
      exact (by simp only [F]; fun_prop : Continuous (F n)).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun a => ?_
      simp only [F]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      have hza : ‖z a‖ ≤ 2 * c * ‖a‖ * ‖y‖ := by
        have h1 : ‖z a‖ = 2 * c * |inner ℝ a y| := by
          simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two, abs_of_pos hc]
        rw [h1]
        have := abs_real_inner_le_norm a y
        nlinarith
      gcongr
    · exact Eventually.of_forall fun a => (Real.summable_pow_div_factorial _).mul_left _
    · have hts : (fun a => ∑' n : ℕ, ‖wt b c h a‖ * ((2 * c * ‖a‖ * ‖y‖) ^ n / n.factorial)) =
          fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖) := by
        funext a
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ,
          ← (NormedSpace.expSeries_div_hasSum_exp (2 * c * ‖a‖ * ‖y‖)).tsum_eq]
      rw [hts]
      have hcw := continuous_wt b c h
      refine Integrable.mono' ((integrable_gauss (E := E) hb).const_mul
        (SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2)))
        (by fun_prop : Continuous fun a => ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)).aestronglyMeasurable
        (Eventually.of_forall fun a => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hC : 0 ≤ SchwartzMap.seminorm ℝ 0 0 h := apply_nonneg _ _
      calc ‖wt b c h a‖ * Real.exp (2 * c * ‖a‖ * ‖y‖)
          ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) *
              Real.exp (2 * c * ‖a‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_right (norm_wt_le b c h a) (by positivity)
        _ = SchwartzMap.seminorm ℝ 0 0 h *
              Real.exp (-((b + c) * ‖a‖ ^ 2) + 2 * c * ‖a‖ * ‖y‖) := by
            rw [Real.exp_add]; ring
        _ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (c * ‖y‖ ^ 2 + -(b * ‖a‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
            nlinarith [sq_nonneg (‖a‖ - ‖y‖)]
        _ = _ := by rw [Real.exp_add]; ring
    · refine Eventually.of_forall fun a => ?_
      rw [Complex.exp_eq_exp_ℂ]
      exact (NormedSpace.expSeries_div_hasSum_exp (z a)).mul_left (wt b c h a)
  have e1 : (fun k => term b c h k y) =
      fun i => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, F i a := by
    funext k
    simp only [term]
    rw [hF]; ring
  have e2 : (∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) =
      Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * ∫ a, wt b c h a * Complex.exp (z a) := by
    rw [← integral_const_mul]
    congr 1; funext a
    have key : Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ)) *
        Complex.exp (z a) = Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [z]
      rw [norm_sub_sq_real, real_inner_comm a y]
      push_cast; ring
    unfold wt
    linear_combination (-(Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a)) * key
  rw [e1, e2]
  exact hsum.mul_left _
end GlobalTheory.ConvSeries
