-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:22.685884+00:00
-- url     : https://prove2.me/submissions/d8135a06-f8c5-4825-9cf9-b2c43f3e75a2

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SchwartzLogDerivLinearGaussian
import Theorems.Thm_GlobalTheory_CompanionTheory_Twist_schwartz_logDeriv_linear_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist
namespace GlobalTheory.CompanionTheory.Twist
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (f₀ : SchwartzMap V ℂ) (hf : f₀ ≠ 0)
    (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) :
    ∃ (c₀ : ℂ) (Q Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), c₀ ≠ 0 ∧ (∀ x, x ≠ 0 → 0 < Q x x) ∧
      ∀ x, f₀ x = c₀ * Complex.exp (-(Q x x : ℂ) - Complex.I * (Q' x x : ℂ)) := by
  have hform := fun y => schwartz_logDeriv_linear_formula f₀ m hm y
  have hc0 : f₀ 0 ≠ 0 := by
    intro h0
    apply hf
    ext x
    simp [hform x, h0]
  refine ⟨f₀ 0, (-(1 / 2 : ℝ)) • m.compr₂ Complex.reLm, (-(1 / 2 : ℝ)) • m.compr₂ Complex.imLm,
    hc0, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, smul_eq_mul]
    by_contra hle
    push Not at hle
    have hre : 0 ≤ (m x x).re := by linarith
    obtain ⟨C, hCpos, hC⟩ := f₀.decay 1 0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hcpos : 0 < ‖f₀ 0‖ := norm_pos_iff.mpr hc0
    set t : ℝ := C / (‖f₀ 0‖ * ‖x‖) + 1 with ht
    have htpos : 0 < t := by positivity
    have hlow : ‖f₀ 0‖ ≤ ‖f₀ (t • x)‖ := by
      rw [hform (t • x), norm_mul, Complex.norm_exp]
      apply le_mul_of_one_le_right (norm_nonneg _)
      apply Real.one_le_exp
      simp only [map_smul, LinearMap.smul_apply, smul_smul, Complex.div_ofNat_re, Complex.smul_re,
        smul_eq_mul]
      have h6 := mul_nonneg (mul_self_nonneg t) hre
      linarith
    have hdec := hC (t • x)
    rw [pow_one, norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at hdec
    have hbig : C < t * ‖x‖ * ‖f₀ 0‖ := by
      have hne : ‖f₀ 0‖ * ‖x‖ ≠ 0 := by positivity
      have heq : t * ‖x‖ * ‖f₀ 0‖ = C + ‖x‖ * ‖f₀ 0‖ := by
        rw [ht]
        field_simp
      rw [heq]
      linarith [mul_pos hxpos hcpos]
    have h7 : t * ‖x‖ * ‖f₀ 0‖ ≤ t * ‖x‖ * ‖f₀ (t • x)‖ :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · intro x
    rw [hform x]
    congr 1
    congr 1
    simp only [LinearMap.smul_apply, LinearMap.compr₂_apply, Complex.reLm_coe, Complex.imLm_coe,
      smul_eq_mul]
    apply Complex.ext <;> simp <;> ring
end GlobalTheory.CompanionTheory.Twist
