-- Prove2me | solution 1 for OAI.Cotype.exists_sector_timed_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:55:07.588107+00:00
-- url     : https://prove2.me/submissions/d2428fac-488c-47b3-aad1-e5d449116fe0

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent

open OAI OAI.Cotype


theorem solution {ρ : ℝ} (hρ1 : 1 < ρ) (hρ2 : ρ < 2) :
    ∃ a B : ℝ, 0 < a ∧ 0 ≤ B ∧
      ∀ z : ℂ, z ≠ 0 → z.re ≤ a*|z.im| →
        ∃ t D : ℝ, 0 < t ∧ 0 ≤ D ∧
          ρ ≤ ‖1-Complex.exp (-(z*(t : ℂ)))‖ ∧
          (∀ s ∈ Set.Icc 0 t, Real.exp (z.re*(s-t)) ≤ D) ∧
          D*t / ‖1-Complex.exp (-(z*(t : ℂ)))‖ ≤ B/‖z‖ := by
  have hρ1' : 0 < ρ - 1 := by linarith
  set a : ℝ := Real.log (1/(ρ-1)) / Real.pi with ha_def
  have hlogpos : 0 < Real.log (1/(ρ-1)) := Real.log_pos (by rw [lt_div_iff₀ hρ1']; linarith)
  have ha : 0 < a := div_pos hlogpos Real.pi_pos
  have hexpa : Real.exp (-(a*Real.pi)) = ρ - 1 := by
    rw [ha_def, div_mul_cancel₀ _ Real.pi_pos.ne', Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num); linarith
  have hlog3p : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨a, Real.pi*(a+2) + 6, ha, by positivity, ?_⟩
  intro z hz hsec
  have hznorm := Complex.norm_le_abs_re_add_abs_im z
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set x := z.re with hx
  set y := z.im with hy
  have hre : ∀ t : ℝ, (-(z*(t:ℂ))).re = -(x*t) := by intro t; simp [Complex.mul_re, hx]
  have him : ∀ t : ℝ, (-(z*(t:ℂ))).im = -(y*t) := by intro t; simp [Complex.mul_im, hy]
  by_cases hcase : x < -|y|
  · -- left case
    have hxneg : x < 0 := by linarith [abs_nonneg y]
    set t := Real.log 3 / (-x) with ht
    have htpos : 0 < t := div_pos hlog3p (by linarith)
    have hxt : -(x*t) = Real.log 3 := by rw [ht]; field_simp; exact div_self hxneg.ne
    have hE : ‖Complex.exp (-(z*(t:ℂ)))‖ = 3 := by
      rw [Complex.norm_exp, hre, hxt, Real.exp_log (by norm_num)]
    have hW : 2 ≤ ‖1 - Complex.exp (-(z*(t:ℂ)))‖ := by
      have := norm_sub_norm_le (Complex.exp (-(z*(t:ℂ)))) 1
      rw [norm_sub_rev] at this; rw [hE, norm_one] at this; linarith
    refine ⟨t, 3, htpos, by norm_num, by linarith, ?_, ?_⟩
    · intro s hs
      have : x*(s-t) ≤ Real.log 3 := by nlinarith [hs.1]
      calc Real.exp (x*(s-t)) ≤ Real.exp (Real.log 3) := Real.exp_le_exp.2 this
        _ = 3 := Real.exp_log (by norm_num)
    · have hWpos : 0 < ‖1 - Complex.exp (-(z*(t:ℂ)))‖ := by linarith
      rw [div_le_div_iff₀ hWpos hzpos]
      have hzx : ‖z‖ ≤ -2*x := by rw [abs_of_neg hxneg] at hznorm; linarith
      have htz : t * ‖z‖ ≤ 2 * Real.log 3 := by
        calc t * ‖z‖ ≤ t * (-2*x) := mul_le_mul_of_nonneg_left hzx htpos.le
          _ = 2 * Real.log 3 := by rw [ht]; field_simp; rw [div_self hxneg.ne]
      have hB : 6 ≤ Real.pi*(a+2) + 6 := by have := Real.pi_pos; nlinarith
      nlinarith
  · push_neg at hcase
    have hy0 : y ≠ 0 := by
      intro h0
      apply hz
      rw [h0, abs_zero] at hcase hsec
      apply Complex.ext
      · show x = 0; linarith
      · exact h0
    have hyp : 0 < |y| := abs_pos.2 hy0
    set t := Real.pi / |y| with ht
    have htpos : 0 < t := div_pos Real.pi_pos hyp
    have hcs : Real.cos (-(y*t)) = -1 ∧ Real.sin (-(y*t)) = 0 := by
      rcases lt_or_gt_of_ne hy0 with h | h
      · have : -(y*t) = Real.pi := by rw [ht, abs_of_neg h]; field_simp
        rw [this]; exact ⟨Real.cos_pi, Real.sin_pi⟩
      · have : -(y*t) = -Real.pi := by rw [ht, abs_of_pos h]; field_simp
        rw [this, Real.cos_neg, Real.sin_neg]; exact ⟨Real.cos_pi, by simp⟩
    have hWeq : 1 - Complex.exp (-(z*(t:ℂ))) = ((1 + Real.exp (-(x*t)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.exp_re, hre, him, hcs.1, Complex.ofReal_re]; ring
      · simp only [Complex.sub_im, Complex.one_im, Complex.exp_im, hre, him, hcs.2, Complex.ofReal_im]; ring
    have hWn : ‖1 - Complex.exp (-(z*(t:ℂ)))‖ = 1 + Real.exp (-(x*t)) := by
      rw [hWeq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hxa : x*t ≤ a*Real.pi := by
      calc x*t ≤ (a*|y|)*t := mul_le_mul_of_nonneg_right hsec htpos.le
        _ = a*Real.pi := by rw [ht]; field_simp
    have hρle : ρ ≤ 1 + Real.exp (-(x*t)) := by
      have : Real.exp (-(a*Real.pi)) ≤ Real.exp (-(x*t)) := Real.exp_le_exp.2 (by linarith)
      linarith
    set D := max 1 (Real.exp (-(x*t))) with hD
    have hDle : D ≤ 1 + Real.exp (-(x*t)) := max_le (by linarith [Real.exp_pos (-(x*t))]) (by linarith)
    refine ⟨t, D, htpos, le_trans zero_le_one (le_max_left _ _), by rw [hWn]; exact hρle, ?_, ?_⟩
    · intro s hs
      have : x*(s-t) ≤ max 0 (-(x*t)) := by
        rcases le_or_gt 0 x with hx0 | hx0
        · exact le_trans (by nlinarith [hs.2]) (le_max_left _ _)
        · exact le_trans (by nlinarith [hs.1]) (le_max_right _ _)
      calc Real.exp (x*(s-t)) ≤ Real.exp (max 0 (-(x*t))) := Real.exp_le_exp.2 this
        _ = D := by
          rw [hD]; rcases le_total 0 (-(x*t)) with h | h
          · rw [max_eq_right h, max_eq_right (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 h)]
          · rw [max_eq_left h, Real.exp_zero, max_eq_left (by rw [← Real.exp_zero]; exact Real.exp_le_exp.2 h)]
    · rw [hWn]
      have hWpos : 0 < 1 + Real.exp (-(x*t)) := by positivity
      rw [div_le_div_iff₀ hWpos hzpos]
      have hxabs : |x| ≤ (a+1)*|y| := by
        rw [abs_le]; constructor <;> nlinarith [abs_nonneg y]
      have hz2 : ‖z‖ ≤ (a+2)*|y| := by linarith
      have htz : t * ‖z‖ ≤ Real.pi*(a+2) := by
        calc t * ‖z‖ ≤ t * ((a+2)*|y|) := mul_le_mul_of_nonneg_left hz2 htpos.le
          _ = Real.pi*(a+2) := by rw [ht]; field_simp
      have hD0 : 0 ≤ D := le_trans zero_le_one (le_max_left _ _)
      calc D * t * ‖z‖ ≤ (1 + Real.exp (-(x*t))) * (t * ‖z‖) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hDle (by positivity)
        _ ≤ (1 + Real.exp (-(x*t))) * (Real.pi*(a+2) + 6) := by
            apply mul_le_mul_of_nonneg_left _ hWpos.le; linarith
        _ = _ := by ring

