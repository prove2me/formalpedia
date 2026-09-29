-- Prove2me | solution 1 for LanglandsTunnell.Converse.dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/033b0b4b-8718-567f-b6b5-5f0857713a2c

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace Ws23K7pt

theorem quasiChar_pos (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : 0 < y) :
    ArchR.quasiChar u a y = ((y : ℝ) : ℂ) ^ u := by
  unfold ArchR.quasiChar
  rw [abs_of_pos hy, sign_pos hy]
  split_ifs <;> simp

theorem quasiChar_neg (u : ℂ) (a : ZMod 2) (y : ℝ) :
    ArchR.quasiChar u a (-y) = (-1 : ℂ) ^ a.val * ArchR.quasiChar u a y := by
  unfold ArchR.quasiChar
  rw [abs_neg, Left.sign_neg]
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) a with rfl | rfl
  · simp
  · simp only [show (1 : ZMod 2) ≠ 0 from by decide, if_false, show (1 : ZMod 2).val = 1 from rfl, pow_one]
    push_cast; ring

theorem pos_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) : ((x : ℝ) : ℂ) ^ z = Complex.exp (z * (Real.log x : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le, mul_comm]

theorem pos_cpow_ne_zero {x : ℝ} (hx : 0 < x) (z : ℂ) : ((x : ℝ) : ℂ) ^ z ≠ 0 := by
  rw [pos_cpow hx]; exact Complex.exp_ne_zero _

theorem zmod2_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with h | h <;> simp [h]

end Ws23K7pt

namespace Ws23K7kit

theorem moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

end Ws23K7kit

namespace Ws25Kit
open LanglandsTunnell.Converse.ArchR Set MeasureTheory

theorem Gc_def : (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) = fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := rfl

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    have h__af := ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
    simp [pow_one] at h__af
    exact h__af
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  rw [h3.deriv]
  push_cast
  ring

private theorem _root_.Ws25Kit.moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

p2m_export "Ws25Kit" "moment_zero"
theorem moment_one (ξ : ℝ) :
    ∫ u : ℝ, ((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      Complex.I * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 1 ξ
  simp only [pow_one, iteratedDeriv_one] at h
  rw [h, deriv_Gc]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_pow_mul_G_mul (k : ℕ) (ξ : ℝ) :
    Integrable (fun u : ℝ => ((u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
  have h0 := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := k)
    (by have := k.cast_nonneg (α := ℝ); linarith)).ofReal (𝕜 := ℂ)
  have h : Integrable (fun x : ℝ => (((x ^ (k : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ)) : ℂ)) := h0
  have h' : Integrable (fun u : ℝ => (u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) := by
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]
  refine h'.mul_bdd (c := 1) (by fun_prop : Continuous fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem x_moment (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (1 - ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) with hf

  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) +
        (Complex.I * ((|y₁| : ℝ) : ℂ)) *
          (((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
    push_cast
    ring
  have hint1 := integrable_pow_mul_G_mul 0 ξ
  have hint2 := integrable_pow_mul_G_mul 1 ξ
  simp only [pow_zero, one_mul] at hint1
  simp only [pow_one] at hint2
  have hscaled : ∫ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add hint1 (hint2.const_mul _), integral_const_mul, moment_zero, moment_one]
    linear_combination (((|y₁| : ℝ) : ℂ) * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ)) * Complex.I_sq
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub

  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (-( ((|y₁| : ℝ) : ℂ)))) * habs'

theorem x_moment0 (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
  have hscaled : ∫ u : ℝ, f (|y₁| * u) = (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
    simp_rw [hpt]; exact moment_zero ξ
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
    rw [hsub]; push_cast; field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x)) = ∫ x, f x from rfl, key, hξ, mul_pow, sq_abs]

theorem affine_moment (a : ℝ) {Y : ℝ} (hY : Y ≠ 0) (c₀ c₁ : ℂ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (x : ℂ)) * psi (a * x) =
      ((|Y| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (a ^ 2 * Y ^ 2))) : ℂ) * (c₀ - c₁ * (a : ℂ) * (Y : ℂ) ^ 2) := by
  have h0 := x_moment0 a hY
  have h1 := x_moment a hY
  have hsplit : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * (c₀ + c₁ * Complex.I * (x : ℂ)) * psi (a * x) =
      (c₀ - c₁) * ((Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * psi (a * x)) +
        c₁ * ((Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (a * x)) := by
    intro x; ring
  have hb : 0 < Real.pi / Y ^ 2 := by positivity
  have hpsi_norm : ∀ x : ℝ, ‖psi (a * x)‖ = 1 := by
    intro x
    rw [psi, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * (((a * x : ℝ)) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hpsi_cont : Continuous fun x : ℝ => psi (a * x) := by
    have : (fun x : ℝ => psi (a * x)) = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((a * x : ℝ)) : ℂ)) := by
      funext x; rw [psi]
    rw [this]; fun_prop
  have hG : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℝ) = Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) := by
    intro x; congr 1; ring
  have hint0 : Integrable (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * psi (a * x)) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq hb) ?_ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul hpsi_cont).aestronglyMeasurable
    · rw [norm_mul, hpsi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG]
  have hint1 : Integrable (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / Y ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (a * x)) := by
    refine Integrable.mono' ((integrable_exp_neg_mul_sq hb).add (integrable_mul_exp_neg_mul_sq hb).norm) ?_ (ae_of_all _ fun x => ?_)
    · exact (((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).mul hpsi_cont).aestronglyMeasurable
    · simp only [Pi.add_apply]
      rw [norm_mul, norm_mul, hpsi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have h1x : ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ≤ 1 + |x| := by
        calc ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (x : ℂ)‖ := norm_add_le _ _
          _ = 1 + |x| := by rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hE : 0 ≤ Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) := Real.exp_nonneg _
      calc Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) * ‖(1 : ℂ) + Complex.I * (x : ℂ)‖
          ≤ Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) * (1 + |x|) := mul_le_mul_of_nonneg_left h1x hE
        _ = Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) + |x| * Real.exp (-(Real.pi / Y ^ 2) * x ^ 2) := by ring
  simp_rw [hsplit]
  rw [integral_add (hint0.const_mul _) (hint1.const_mul _), integral_const_mul, integral_const_mul, h0, h1]
  push_cast
  ring

theorem x_step (a a₁ : ℝ) {a₂ y₁ : ℝ} (ha₂ : a₂ ≠ 0) (hy₁ : y₁ ≠ 0) (y₂ : ℝ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) * psi (a * x) =
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) * ((|a₂ * y₁| : ℝ) : ℂ) *
        (Real.exp (-(Real.pi * (a ^ 2 * (a₂ * y₁) ^ 2))) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) := by
  have hY : a₂ * y₁ ≠ 0 := mul_ne_zero ha₂ hy₁
  have hE : ∀ x : ℝ, ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℝ) : ℂ) =
      (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) * (Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) := by
    intro x; rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 1; congr 1; field_simp; ring
  have hB : ∀ x : ℝ, (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) =
      (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ))) +
        (((y₁⁻¹ : ℝ) : ℂ) * (a₂⁻¹ : ℂ) * ((y₁⁻¹ : ℝ) : ℂ)) * Complex.I * (x : ℂ) := by
    intro x; push_cast; ring
  have key := affine_moment a hY (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ)))
    (((y₁⁻¹ : ℝ) : ℂ) * (a₂⁻¹ : ℂ) * ((y₁⁻¹ : ℝ) : ℂ))
  calc _ = ∫ x : ℝ, (Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
        ((Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) *
          ((((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ))) +
            (((y₁⁻¹ : ℝ) : ℂ) * (a₂⁻¹ : ℂ) * ((y₁⁻¹ : ℝ) : ℂ)) * Complex.I * (x : ℂ)) * psi (a * x)) := by
          congr 1; funext x; rw [hE x, hB x]; ring
    _ = _ := by
      rw [integral_const_mul, key]
      have h1 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁
      have h2 : ((a₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha₂
      push_cast
      field_simp

end Ws25Kit

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace Ws23K7fib

open LanglandsTunnell.Converse.ArchR

theorem gauss_psi (a : ℝ) {w : ℝ} (hw : w ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / w ^ 2))) : ℂ) * psi (a * x) =
      ((|w| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * w ^ 2)) : ℂ) := by
  have hwp : 0 < |w| := abs_pos.2 hw
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / w ^ 2))) : ℂ) * psi (a * x) with hf
  have hpt : ∀ u : ℝ, f (|w| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((a * |w| : ℝ) : ℂ) * (u : ℂ)) := by
    intro u
    have hsq : (|w| * u) ^ 2 / w ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (a * (|w| * u)) = Complex.exp (2 * Real.pi * Complex.I * ((a * |w| : ℝ) : ℂ) * (u : ℂ)) := by
      rw [psi]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
  have hscaled : ∫ u : ℝ, f (|w| * u) = (Real.exp (-(Real.pi * (a * |w|) ^ 2)) : ℂ) := by
    simp_rw [hpt]; exact Ws23K7kit.moment_zero (a * |w|)
  have hsub := Measure.integral_comp_mul_left f |w|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|w| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hwp.ne'
  have key : ∫ x, f x = ((|w| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (a * |w|) ^ 2)) : ℂ) := by
    rw [hsub]; push_cast; field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / w ^ 2))) : ℂ) * psi (a * x)) = ∫ x, f x from rfl, key]
  congr 1
  rw [mul_pow, sq_abs]; push_cast; ring

theorem setIntegral_Ioi_comp_inv_mul (g : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi (0 : ℝ), g y = ∫ p in Ioi (0 : ℝ), (((c * p ^ 2)⁻¹ : ℝ) : ℂ) * g ((c * p)⁻¹) := by

  have h1 := integral_comp_rpow_Ioi g (show (-1 : ℝ) ≠ 0 by norm_num)
  have h1' : ∫ x in Ioi (0 : ℝ), (((x ^ 2)⁻¹ : ℝ) : ℂ) * g x⁻¹ = ∫ y in Ioi (0 : ℝ), g y := by
    rw [← h1]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx : 0 < x := hx
    rw [show |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) = (x ^ 2)⁻¹ by
      rw [show ((-1 : ℝ) - 1) = -(2 : ℝ) by norm_num, Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]; simp,
      Real.rpow_neg_one, Complex.real_smul]
  rw [← h1']
  have h2 := integral_comp_mul_left_Ioi (fun x : ℝ => (((x ^ 2)⁻¹ : ℝ) : ℂ) * g x⁻¹) 0 hc
  rw [mul_zero] at h2
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [show (∫ x in Ioi (0 : ℝ), (((x ^ 2)⁻¹ : ℝ) : ℂ) * g x⁻¹) = (c : ℂ) * ∫ p in Ioi (0 : ℝ), ((((c * p) ^ 2)⁻¹ : ℝ) : ℂ) * g (c * p)⁻¹ by
    rw [h2, Complex.real_smul]; push_cast; field_simp [hc0]]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun p hp => ?_)
  have hp : 0 < p := hp
  push_cast
  field_simp

theorem integral_comp_inv_mul (g : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    ∫ y : ℝ, g y = ∫ q : ℝ, (((c * q ^ 2)⁻¹ : ℝ) : ℂ) * g ((c * q)⁻¹) := by
  set S : Set ℝ := {q : ℝ | q ≠ 0} with hS
  have hSm : MeasurableSet S := by
    rw [hS, show {q : ℝ | q ≠ 0} = ({0} : Set ℝ)ᶜ by ext; simp]; exact (measurableSet_singleton 0).compl
  have hSae : ∀ᵐ q : ℝ, q ∈ S := by
    have h : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    exact Filter.Eventually.mono h fun t ht => by simpa [hS] using ht
  have hres : (volume : Measure ℝ).restrict S = volume := Measure.restrict_eq_self_of_ae_mem hSae
  have hderiv : ∀ q ∈ S, HasDerivWithinAt (fun q : ℝ => (c * q)⁻¹) (-(c * q ^ 2)⁻¹) S q := by
    intro q hq
    have hq : q ≠ 0 := hq
    have h := ((hasDerivAt_id q).const_mul c).inv (mul_ne_zero hc.ne' hq)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp; field_simp
  have hinj : InjOn (fun q : ℝ => (c * q)⁻¹) S := by
    intro x _ y _ hxy
    have := congrArg Inv.inv hxy
    simp only [inv_inv] at this
    exact mul_left_cancel₀ hc.ne' this
  have himg : (fun q : ℝ => (c * q)⁻¹) '' S = S := by
    ext y; constructor
    · rintro ⟨q, hq, rfl⟩; exact inv_ne_zero (mul_ne_zero hc.ne' hq)
    · intro hy; refine ⟨(c * y)⁻¹, inv_ne_zero (mul_ne_zero hc.ne' hy), ?_⟩; field_simp
  have key := integral_image_eq_integral_abs_deriv_smul hSm hderiv hinj g
  rw [himg, hres] at key
  rw [key, ← hres]
  refine setIntegral_congr_fun hSm (fun q hq => ?_)
  have hq : q ≠ 0 := hq
  have hpos : 0 < c * q ^ 2 := by positivity
  rw [abs_neg, abs_of_pos (inv_pos.2 hpos), Complex.real_smul]

end Ws23K7fib

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace Ws25K7fibxM

theorem x_int {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℝ) (u₀ : ℂ) (a₀ : ZMod 2) (a₁ a₂ : ℝ) (ha₂ : 0 < a₂)
    {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (y₂ : ℝ) :
    ∫ x : ℝ, ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) =
      ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (((y₂) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * (((y₂)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by
  have hpt : ∀ x : ℝ, ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) =
      ((((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
          (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) * ArchR.psi (a * x)) := by
    intro x; ring
  simp_rw [hpt]
  rw [integral_const_mul, Ws25Kit.x_step a a₁ ha₂.ne' hy₁ y₂]
  ring

end Ws25K7fibxM

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace Ws25K7fibaM

theorem quasiChar_of_neg (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : y < 0) :
    ArchR.quasiChar u a y = (-1 : ℂ) ^ a.val * (((-y) : ℝ) : ℂ) ^ u := by
  have h := Ws23K7pt.quasiChar_neg u a (-y)
  rw [neg_neg] at h
  rw [h, Ws23K7pt.quasiChar_pos _ _ (neg_pos.2 hy)]

theorem inv_cpow_pos {x : ℝ} (hx : 0 < x) (z : ℂ) : (((x⁻¹) : ℝ) : ℂ) ^ z = (((x : ℝ) : ℂ) ^ z)⁻¹ := by
  rw [Ws23K7pt.pos_cpow (inv_pos.2 hx), Ws23K7pt.pos_cpow hx, Real.log_inv, ← Complex.exp_neg]
  congr 1; push_cast; ring

theorem mul_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (((x * y) : ℝ) : ℂ) ^ z = ((x : ℝ) : ℂ) ^ z * ((y : ℝ) : ℂ) ^ z := by
  rw [Ws23K7pt.pos_cpow (mul_pos hx hy), Ws23K7pt.pos_cpow hx, Ws23K7pt.pos_cpow hy, Real.log_mul hx.ne' hy.ne',
    ← Complex.exp_add]
  congr 1; push_cast; ring

theorem div_cpow_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    (((x / y) : ℝ) : ℂ) ^ z = ((x : ℝ) : ℂ) ^ z * ((((y : ℝ) : ℂ) ^ z)⁻¹) := by
  rw [Ws23K7pt.pos_cpow (div_pos hx hy), Ws23K7pt.pos_cpow hx, Ws23K7pt.pos_cpow hy, Real.log_div hx.ne' hy.ne',
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem quasiChar_of_neg' (u : ℂ) (a : ZMod 2) {y : ℝ} (hy : 0 < y) :
    ArchR.quasiChar u a (-y) = (-1 : ℂ) ^ a.val * ((y : ℝ) : ℂ) ^ u := by
  rw [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos _ _ hy]

theorem alg_pp {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : 0 < a₁) (hq : 0 < q) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 - (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  have hne : ∀ {x : ℝ}, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun hx => Complex.ofReal_ne_zero.2 hx.ne'
  have ha₁' : a₁ ≠ 0 := ha₁.ne'
  have hq' : q ≠ 0 := hq.ne'
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁'

  have hdw : ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹) = ArchR.diagOne (a * |(a₁ / a₂)| * p / q) := by
    congr 1; rw [abs_div, abs_of_pos ha₂]; field_simp
  rw [hdw, show -a₁ / a₂ = -(a₁ / a₂) by ring]
  have g1 : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) =
      Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) * Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) := by
    rw [← Real.exp_add]; congr 1
    rw [div_pow, ← sq_abs a₁]; field_simp; ring
  have g2 : Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) := by
    congr 1; rw [← sq_abs a₁]; field_simp
  have g3 : Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) := by
    congr 1; field_simp
  rw [g1, g2, g3]
  rw [show (2 * s - cP - P₂.centralExponent + 1 : ℂ) = (s - 1 / 2) + (s - 1 / 2) - cP - P₂.centralExponent + 2 by ring,
    show (s - 5 / 2 - cP - P₂.centralExponent : ℂ) = (s - 1 / 2) - 2 - cP - P₂.centralExponent by ring]
  set e₀ : ℂ := s - 1 / 2 with he₀
  obtain ⟨A, hA, rfl⟩ : ∃ A : ℝ, 0 < A ∧ a₁ = A := ⟨a₁, ha₁, rfl⟩
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℝ, 0 < Q ∧ q = Q := ⟨q, hq, rfl⟩
  have z1 := hne hA; have z2 := hne ha₂; have z3 := hne hQ; have z4 := hne hp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have n1 := Ws23K7pt.pos_cpow_ne_zero hA e₀; have n2 := Ws23K7pt.pos_cpow_ne_zero ha₂ e₀
  have n3 := Ws23K7pt.pos_cpow_ne_zero hA u₀; have n4 := Ws23K7pt.pos_cpow_ne_zero ha₂ u₀
  have n5 := Ws23K7pt.pos_cpow_ne_zero hQ u₀; have n6 := Ws23K7pt.pos_cpow_ne_zero hp u₀
  have n7 := Ws23K7pt.pos_cpow_ne_zero hA cP; have n8 := Ws23K7pt.pos_cpow_ne_zero ha₂ cP
  have n9 := Ws23K7pt.pos_cpow_ne_zero hA P₂.centralExponent; have n10 := Ws23K7pt.pos_cpow_ne_zero ha₂ P₂.centralExponent
  have n11 := Ws23K7pt.pos_cpow_ne_zero hp P₂.centralExponent
  simp only [neg_mul, mul_neg, neg_neg, inv_neg, abs_neg, neg_div, div_neg, mul_inv, inv_inv, even_two, Even.neg_pow,
    abs_mul, abs_inv, abs_div, abs_of_pos hA, abs_of_pos ha₂, abs_of_pos hQ, abs_of_pos hp]
  simp (disch := positivity) only [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos, ArchR.centralChar,
    Complex.cpow_zero, mul_one, one_mul, neg_neg]
  simp (disch := positivity) only [mul_cpow_pos, inv_cpow_pos, div_cpow_pos]
  simp only [Complex.cpow_add _ _ z1, Complex.cpow_add _ _ z2, Complex.cpow_add _ _ z3, Complex.cpow_add _ _ z4,
    Complex.cpow_sub _ _ z1, Complex.cpow_sub _ _ z2, Complex.cpow_sub _ _ z3, Complex.cpow_sub _ _ z4,
    Complex.cpow_one, Complex.cpow_ofNat]
  rcases Ws23K7pt.zmod2_cases a₀ with rfl | rfl <;> rcases Ws23K7pt.zmod2_cases sP with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one, zpow_zero, zpow_one] <;>
    (push_cast; field_simp; try ring)

theorem alg_np {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : a₁ < 0) (hq : 0 < q) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 - (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  have hne : ∀ {x : ℝ}, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun hx => Complex.ofReal_ne_zero.2 hx.ne'
  have ha₁' : a₁ ≠ 0 := ha₁.ne
  have hq' : q ≠ 0 := hq.ne'
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁'

  have hdw : ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹) = ArchR.diagOne (a * |(a₁ / a₂)| * p / q) := by
    congr 1; rw [abs_div, abs_of_pos ha₂]; field_simp
  rw [hdw, show -a₁ / a₂ = -(a₁ / a₂) by ring]
  have g1 : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) =
      Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) * Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) := by
    rw [← Real.exp_add]; congr 1
    rw [div_pow, ← sq_abs a₁]; field_simp; ring
  have g2 : Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) := by
    congr 1; rw [← sq_abs a₁]; field_simp
  have g3 : Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) := by
    congr 1; field_simp
  rw [g1, g2, g3]
  rw [show (2 * s - cP - P₂.centralExponent + 1 : ℂ) = (s - 1 / 2) + (s - 1 / 2) - cP - P₂.centralExponent + 2 by ring,
    show (s - 5 / 2 - cP - P₂.centralExponent : ℂ) = (s - 1 / 2) - 2 - cP - P₂.centralExponent by ring]
  set e₀ : ℂ := s - 1 / 2 with he₀
  obtain ⟨A, hA, rfl⟩ : ∃ A : ℝ, 0 < A ∧ a₁ = -A := ⟨-a₁, neg_pos.2 ha₁, by ring⟩
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℝ, 0 < Q ∧ q = Q := ⟨q, hq, rfl⟩
  have z1 := hne hA; have z2 := hne ha₂; have z3 := hne hQ; have z4 := hne hp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have n1 := Ws23K7pt.pos_cpow_ne_zero hA e₀; have n2 := Ws23K7pt.pos_cpow_ne_zero ha₂ e₀
  have n3 := Ws23K7pt.pos_cpow_ne_zero hA u₀; have n4 := Ws23K7pt.pos_cpow_ne_zero ha₂ u₀
  have n5 := Ws23K7pt.pos_cpow_ne_zero hQ u₀; have n6 := Ws23K7pt.pos_cpow_ne_zero hp u₀
  have n7 := Ws23K7pt.pos_cpow_ne_zero hA cP; have n8 := Ws23K7pt.pos_cpow_ne_zero ha₂ cP
  have n9 := Ws23K7pt.pos_cpow_ne_zero hA P₂.centralExponent; have n10 := Ws23K7pt.pos_cpow_ne_zero ha₂ P₂.centralExponent
  have n11 := Ws23K7pt.pos_cpow_ne_zero hp P₂.centralExponent
  simp only [neg_mul, mul_neg, neg_neg, inv_neg, abs_neg, neg_div, div_neg, mul_inv, inv_inv, even_two, Even.neg_pow,
    abs_mul, abs_inv, abs_div, abs_of_pos hA, abs_of_pos ha₂, abs_of_pos hQ, abs_of_pos hp]
  simp (disch := positivity) only [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos, ArchR.centralChar,
    Complex.cpow_zero, mul_one, one_mul, neg_neg]
  simp (disch := positivity) only [mul_cpow_pos, inv_cpow_pos, div_cpow_pos]
  simp only [Complex.cpow_add _ _ z1, Complex.cpow_add _ _ z2, Complex.cpow_add _ _ z3, Complex.cpow_add _ _ z4,
    Complex.cpow_sub _ _ z1, Complex.cpow_sub _ _ z2, Complex.cpow_sub _ _ z3, Complex.cpow_sub _ _ z4,
    Complex.cpow_one, Complex.cpow_ofNat]
  rcases Ws23K7pt.zmod2_cases a₀ with rfl | rfl <;> rcases Ws23K7pt.zmod2_cases sP with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one, zpow_zero, zpow_one] <;>
    (push_cast; field_simp; try ring)

theorem alg_pn {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : 0 < a₁) (hq : q < 0) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 - (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  have hne : ∀ {x : ℝ}, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun hx => Complex.ofReal_ne_zero.2 hx.ne'
  have ha₁' : a₁ ≠ 0 := ha₁.ne'
  have hq' : q ≠ 0 := hq.ne
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁'

  have hdw : ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹) = ArchR.diagOne (a * |(a₁ / a₂)| * p / q) := by
    congr 1; rw [abs_div, abs_of_pos ha₂]; field_simp
  rw [hdw, show -a₁ / a₂ = -(a₁ / a₂) by ring]
  have g1 : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) =
      Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) * Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) := by
    rw [← Real.exp_add]; congr 1
    rw [div_pow, ← sq_abs a₁]; field_simp; ring
  have g2 : Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) := by
    congr 1; rw [← sq_abs a₁]; field_simp
  have g3 : Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) := by
    congr 1; field_simp
  rw [g1, g2, g3]
  rw [show (2 * s - cP - P₂.centralExponent + 1 : ℂ) = (s - 1 / 2) + (s - 1 / 2) - cP - P₂.centralExponent + 2 by ring,
    show (s - 5 / 2 - cP - P₂.centralExponent : ℂ) = (s - 1 / 2) - 2 - cP - P₂.centralExponent by ring]
  set e₀ : ℂ := s - 1 / 2 with he₀
  obtain ⟨A, hA, rfl⟩ : ∃ A : ℝ, 0 < A ∧ a₁ = A := ⟨a₁, ha₁, rfl⟩
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℝ, 0 < Q ∧ q = -Q := ⟨-q, neg_pos.2 hq, by ring⟩
  have z1 := hne hA; have z2 := hne ha₂; have z3 := hne hQ; have z4 := hne hp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have n1 := Ws23K7pt.pos_cpow_ne_zero hA e₀; have n2 := Ws23K7pt.pos_cpow_ne_zero ha₂ e₀
  have n3 := Ws23K7pt.pos_cpow_ne_zero hA u₀; have n4 := Ws23K7pt.pos_cpow_ne_zero ha₂ u₀
  have n5 := Ws23K7pt.pos_cpow_ne_zero hQ u₀; have n6 := Ws23K7pt.pos_cpow_ne_zero hp u₀
  have n7 := Ws23K7pt.pos_cpow_ne_zero hA cP; have n8 := Ws23K7pt.pos_cpow_ne_zero ha₂ cP
  have n9 := Ws23K7pt.pos_cpow_ne_zero hA P₂.centralExponent; have n10 := Ws23K7pt.pos_cpow_ne_zero ha₂ P₂.centralExponent
  have n11 := Ws23K7pt.pos_cpow_ne_zero hp P₂.centralExponent
  simp only [neg_mul, mul_neg, neg_neg, inv_neg, abs_neg, neg_div, div_neg, mul_inv, inv_inv, even_two, Even.neg_pow,
    abs_mul, abs_inv, abs_div, abs_of_pos hA, abs_of_pos ha₂, abs_of_pos hQ, abs_of_pos hp]
  simp (disch := positivity) only [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos, ArchR.centralChar,
    Complex.cpow_zero, mul_one, one_mul, neg_neg]
  simp (disch := positivity) only [mul_cpow_pos, inv_cpow_pos, div_cpow_pos]
  simp only [Complex.cpow_add _ _ z1, Complex.cpow_add _ _ z2, Complex.cpow_add _ _ z3, Complex.cpow_add _ _ z4,
    Complex.cpow_sub _ _ z1, Complex.cpow_sub _ _ z2, Complex.cpow_sub _ _ z3, Complex.cpow_sub _ _ z4,
    Complex.cpow_one, Complex.cpow_ofNat]
  rcases Ws23K7pt.zmod2_cases a₀ with rfl | rfl <;> rcases Ws23K7pt.zmod2_cases sP with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one, zpow_zero, zpow_one] <;>
    (push_cast; field_simp; try ring)

theorem alg_nn {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : a₁ < 0) (hq : q < 0) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 - (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  have hne : ∀ {x : ℝ}, 0 < x → ((x : ℝ) : ℂ) ≠ 0 := fun hx => Complex.ofReal_ne_zero.2 hx.ne'
  have ha₁' : a₁ ≠ 0 := ha₁.ne
  have hq' : q ≠ 0 := hq.ne
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁'

  have hdw : ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹) = ArchR.diagOne (a * |(a₁ / a₂)| * p / q) := by
    congr 1; rw [abs_div, abs_of_pos ha₂]; field_simp
  rw [hdw, show -a₁ / a₂ = -(a₁ / a₂) by ring]
  have g1 : Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) =
      Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) * Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) := by
    rw [← Real.exp_add]; congr 1
    rw [div_pow, ← sq_abs a₁]; field_simp; ring
  have g2 : Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) := by
    congr 1; rw [← sq_abs a₁]; field_simp
  have g3 : Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) = Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) := by
    congr 1; field_simp
  rw [g1, g2, g3]
  rw [show (2 * s - cP - P₂.centralExponent + 1 : ℂ) = (s - 1 / 2) + (s - 1 / 2) - cP - P₂.centralExponent + 2 by ring,
    show (s - 5 / 2 - cP - P₂.centralExponent : ℂ) = (s - 1 / 2) - 2 - cP - P₂.centralExponent by ring]
  set e₀ : ℂ := s - 1 / 2 with he₀
  obtain ⟨A, hA, rfl⟩ : ∃ A : ℝ, 0 < A ∧ a₁ = -A := ⟨-a₁, neg_pos.2 ha₁, by ring⟩
  obtain ⟨Q, hQ, rfl⟩ : ∃ Q : ℝ, 0 < Q ∧ q = -Q := ⟨-q, neg_pos.2 hq, by ring⟩
  have z1 := hne hA; have z2 := hne ha₂; have z3 := hne hQ; have z4 := hne hp
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have n1 := Ws23K7pt.pos_cpow_ne_zero hA e₀; have n2 := Ws23K7pt.pos_cpow_ne_zero ha₂ e₀
  have n3 := Ws23K7pt.pos_cpow_ne_zero hA u₀; have n4 := Ws23K7pt.pos_cpow_ne_zero ha₂ u₀
  have n5 := Ws23K7pt.pos_cpow_ne_zero hQ u₀; have n6 := Ws23K7pt.pos_cpow_ne_zero hp u₀
  have n7 := Ws23K7pt.pos_cpow_ne_zero hA cP; have n8 := Ws23K7pt.pos_cpow_ne_zero ha₂ cP
  have n9 := Ws23K7pt.pos_cpow_ne_zero hA P₂.centralExponent; have n10 := Ws23K7pt.pos_cpow_ne_zero ha₂ P₂.centralExponent
  have n11 := Ws23K7pt.pos_cpow_ne_zero hp P₂.centralExponent
  simp only [neg_mul, mul_neg, neg_neg, inv_neg, abs_neg, neg_div, div_neg, mul_inv, inv_inv, even_two, Even.neg_pow,
    abs_mul, abs_inv, abs_div, abs_of_pos hA, abs_of_pos ha₂, abs_of_pos hQ, abs_of_pos hp]
  simp (disch := positivity) only [Ws23K7pt.quasiChar_neg, Ws23K7pt.quasiChar_pos, ArchR.centralChar,
    Complex.cpow_zero, mul_one, one_mul, neg_neg]
  simp (disch := positivity) only [mul_cpow_pos, inv_cpow_pos, div_cpow_pos]
  simp only [Complex.cpow_add _ _ z1, Complex.cpow_add _ _ z2, Complex.cpow_add _ _ z3, Complex.cpow_add _ _ z4,
    Complex.cpow_sub _ _ z1, Complex.cpow_sub _ _ z2, Complex.cpow_sub _ _ z3, Complex.cpow_sub _ _ z4,
    Complex.cpow_one, Complex.cpow_ofNat]
  rcases Ws23K7pt.zmod2_cases a₀ with rfl | rfl <;> rcases Ws23K7pt.zmod2_cases sP with rfl | rfl <;>
    simp only [show (0 : ZMod 2).val = 0 from rfl, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one, zpow_zero, zpow_one] <;>
    (push_cast; field_simp; try ring)

theorem alg {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) {q p : ℝ} (hp : 0 < p) (ha₁ : a₁ ≠ 0) (hq : q ≠ 0) :
    ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((((a₂ * q ^ 2)⁻¹ : ℝ) : ℂ) * ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / (a₂ * q)⁻¹ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            (((((a₂ * q)⁻¹)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ ((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹ * (((|((a₂ * q)⁻¹ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * (a₂ * q)⁻¹| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * (a₂ * q)⁻¹) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * (a₂ * q)⁻¹ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|(a₂ * q)⁻¹ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) =
    (((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ)) *
      ((((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + (((a₁ / a₂) : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ 2 - (a : ℂ) * ((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)))) := by
  rcases lt_or_gt_of_ne ha₁ with h1 | h1 <;> rcases lt_or_gt_of_ne hq with h2 | h2
  · exact alg_nn D W a u₀ cP a₀ sP k s a₁ a₂ ha₂ hp h1 h2
  · exact alg_np D W a u₀ cP a₀ sP k s a₁ a₂ ha₂ hp h1 h2
  · exact alg_pn D W a u₀ cP a₀ sP k s a₁ a₂ ha₂ hp h1 h2
  · exact alg_pp D W a u₀ cP a₀ sP k s a₁ a₂ ha₂ hp h1 h2

end Ws25K7fibaM

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory Set

namespace Ws23K7fibm

theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  exact Filter.Eventually.mono h fun t ht => by simpa using ht

end Ws23K7fibm

open Ws23K7fibm in
theorem solution
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (k : ℤ) (s : ℂ)
    (a₁ a₂ : ℝ) (ha₁ : a₁ ≠ 0) (ha₂ : 0 < a₂) :
    (((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (k : ℤ) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) *
                      W (-a₁ / a₂))) *
                  (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
                    (((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ) * Complex.I ^ (k : ℤ) * (((a₂⁻¹ : ℝ)) : ℂ) *
        ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
        (((a₂ : ℝ) : ℂ) ^ (2 * s - cP - P₂.centralExponent + 1) * (Real.exp (-(Real.pi * a₂ ^ 2 * q ^ 2)) : ℂ)) *
        ((ArchR.quasiChar 0 sP (-(a₁ / a₂)) * ArchR.quasiChar 0 a₀ (-(a₁ / a₂)) * ArchR.quasiChar 0 1 (a₁ / a₂) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(a₁ / a₂)) * ((a : ℂ) + ((a₁ / a₂ : ℝ) : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (a₁ / a₂) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(a₁ / a₂)| * p / q))) *
          ((((|(a₁ / a₂)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (a₁ / a₂) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) := by
  have ha1 : 0 < |a₁| := abs_pos.2 ha₁

  have hX : (∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
          ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (x ^ 2 / y₁ ^ 2 + 1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            (((y₁⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (y₂ : ℂ) + (a₂⁻¹ : ℂ) * ((y₂⁻¹ : ℝ) : ℂ) + Complex.I * (a₂⁻¹ : ℂ) * (((x / y₁ : ℝ)) : ℂ))) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          (ArchR.psi (a * x) * (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (((y₂) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * (((y₂)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with y₁ hy₁
    refine setIntegral_congr_fun measurableSet_Ioi (fun y₂ _ => ?_)
    exact Ws25K7fibxM.x_int D a u₀ a₀ a₁ a₂ ha₂ hy₁ y₂
  have hS2 : (∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (((y₂) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * (((y₂)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ y₁ : ℝ, ∫ p in Set.Ioi (0 : ℝ), ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * (|a₁| * p)⁻¹)⁻¹ * (((|(y₁ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|y₁ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ))) := by
    refine integral_congr_ae (ae_of_all _ (fun y₁ => ?_))
    exact Ws23K7fib.setIntegral_Ioi_comp_inv_mul (fun y₂ => ((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / y₂ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * y₂| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * (((y₂) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * (((y₂)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * y₂ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / y₂))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) ha1
  have hS3 := Ws23K7fib.integral_comp_inv_mul (fun y₁ : ℝ => ∫ p in Set.Ioi (0 : ℝ), ((((|a₁| * p ^ 2)⁻¹ : ℝ) : ℂ) *
        (((Real.exp (-(Real.pi * (a₂⁻¹ ^ 2 * (1 / (|a₁| * p)⁻¹ ^ 2) + 1 / y₁ ^ 2))) : ℂ) *
            (((a₁ ^ 2 * |y₁ * (|a₁| * p)⁻¹| : ℝ)) : ℂ) *
            ((((y₁)⁻¹ : ℝ) : ℂ) * ((a : ℂ) * (a₁ : ℂ) * ((((|a₁| * p)⁻¹) : ℝ) : ℂ) + (a₂⁻¹ : ℂ) * ((((|a₁| * p)⁻¹)⁻¹ : ℝ) : ℂ)) - (a : ℂ) * (a₂ : ℂ)) *
            (Real.exp (-(Real.pi * a ^ 2 * a₁ ^ 2 * (|a₁| * p)⁻¹ ^ 2)) : ℂ)) *
          (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * (|a₁| * p)⁻¹)⁻¹ * (((|(y₁ * (|a₁| * p)⁻¹)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ)) *
          ((((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 * (a₂ * y₁) ^ 2)) : ℂ)) *
            (ArchR.centralChar P₂ (|a₁| * p)⁻¹ * ((|(|a₁| * p)⁻¹| : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * y₁ / (|a₁| * p)⁻¹))) *
          (((|a₁| * p)⁻¹ ^ 2 * (|y₁ * (|a₁| * p)⁻¹| ^ 4)⁻¹ : ℝ) : ℂ)))) ha₂
  rw [hX, hS2, hS3]
  beta_reduce
  have key : ∀ INT : ℂ, ((((|a₁ * a₂| : ℝ) : ℂ) *
                    (Complex.I ^ (k : ℤ) *
                      ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
                        ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) *
                      W (-a₁ / a₂))) *
                  (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
                    (((2 * Real.pi : ℝ) : ℂ) * INT)) *
                  (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ) = ((((|a₁ * a₂| : ℝ) : ℂ) * (Complex.I ^ (k : ℤ) * ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (cP + 1)) *
      ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (sP.val : ℤ)) * W (-a₁ / a₂))) *
      ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) * ((2 * Real.pi : ℝ) : ℂ) * (((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)) * INT := fun INT => by ring
  rw [key, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with q hq
  rw [← mul_assoc, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun p hp => ?_)
  rw [mul_assoc]
  exact Ws25K7fibaM.alg D W a u₀ cP a₀ sP k s a₁ a₂ ha₂ hp ha₁ hq

#print axioms solution

end S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic
end P2MW
export P2MW.S_LanglandsTunnell_Converse_dualTorusPair_iwasawa_fibre_eq_const_mul_integral_torusQuadruple_blockHarmonic (solution)
