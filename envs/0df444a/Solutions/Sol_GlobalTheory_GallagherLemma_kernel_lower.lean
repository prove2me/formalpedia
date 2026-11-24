-- Prove2me | solution 1 for GlobalTheory.GallagherLemma.kernel_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:19.634332+00:00
-- url     : https://prove2.me/submissions/4a00bfb6-0083-44b4-a14e-88a9378612f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real
open GlobalTheory GlobalTheory.GallagherLemma
namespace GlobalTheory.GallagherLemma
theorem _root_.solution (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hc : Continuous fun u : ℝ => cexp ((s * u : ℝ) * I) := by fun_prop
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable (μ := volume) 0 δ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  calc δ / 2 = ∫ u in (0 : ℝ)..δ, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hδ (by simp)
        ((Complex.continuous_re.comp hc).intervalIntegrable _ _) fun u hu => ?_
      rw [exp_ofReal_mul_I_re]
      have h1 : |s * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hu.1]
        exact le_trans (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)) hs
      have h2 := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have h3 : (s * u) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (s * u)]
      linarith
end GlobalTheory.GallagherLemma
