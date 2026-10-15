-- Prove2me | solution 1 for MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:20:24.165033+00:00
-- url     : https://prove2.me/submissions/9f68a57f-5e39-4318-8040-89cc6e65fec3

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set
set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x z : E) :
    ENNReal.ofReal |f x - f z| ≤ ENNReal.ofReal ‖z - x‖ *
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖gradient f (x + t • (z - x))‖) := by
  let γ : ℝ → E := fun t => x + t • (z - x)
  let D : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (z - x)
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous D :=
    ((hf.continuous_fderiv (by norm_num)).comp hγ).clm_apply continuous_const
  have hderiv (t : ℝ) : HasDerivAt (fun s => f (γ s)) (D t) t := by
    have hp : HasDerivAt γ (z - x) t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
    exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t hp
  have hFTC : (∫ t in (0 : ℝ)..1, D t) = f z - f x := by
    simpa [γ] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hD.intervalIntegrable 0 1)
  have hnorm (t : ℝ) : ‖D t‖ ≤ ‖z - x‖ * ‖gradient f (γ t)‖ := by
    dsimp [D]
    rw [← inner_gradient_left]
    simpa [mul_comm] using norm_inner_le_norm (𝕜 := ℝ) (gradient f (γ t)) (z - x)
  calc
    ENNReal.ofReal |f x - f z| = ‖∫ t in Icc (0 : ℝ) 1, D t‖ₑ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hFTC]
      simp [Real.enorm_eq_ofReal_abs, abs_sub_comm]
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖D t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal ‖z - x‖ * ENNReal.ofReal ‖gradient f (γ t)‖ := by
      apply lintegral_mono
      intro t
      change ‖D t‖ₑ ≤ ENNReal.ofReal ‖z - x‖ * ENNReal.ofReal ‖gradient f (γ t)‖
      simpa only [ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)] using
        ENNReal.ofReal_le_ofReal (hnorm t)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

