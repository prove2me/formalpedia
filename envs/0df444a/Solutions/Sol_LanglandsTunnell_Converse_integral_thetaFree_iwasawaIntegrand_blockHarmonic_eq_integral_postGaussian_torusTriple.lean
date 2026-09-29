-- Prove2me | solution 1 for LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/98d45a4d-ae31-5add-a643-9ff07b28daae

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple

set_option autoImplicit false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

noncomputable section

namespace Ws23K7kit

open LanglandsTunnell.Converse.ArchR Set

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

theorem moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

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

end Ws23K7kit

namespace Ws25K7majx

open Ws23K7kit LanglandsTunnell.Converse.ArchR

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

theorem x_moment_major (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (y₂ : ℝ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        ((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - c * y₁ : ℝ)) : ℂ) := by

  have hsplit : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        ((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) * psi (c * x) =
      (((1 / y₁ : ℝ)) : ℂ) * ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x)) +
      (((1 / y₂ : ℝ)) : ℂ) * ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x)) := by
    intro x; push_cast; ring
  have hb : 0 < Real.pi / y₁ ^ 2 := by positivity
  have hpsi_norm : ∀ x : ℝ, ‖psi (c * x)‖ = 1 := by
    intro x
    rw [psi, Complex.norm_exp]
    have : (2 * (Real.pi : ℂ) * Complex.I * (((c * x : ℝ)) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  have hpsi_cont : Continuous fun x : ℝ => psi (c * x) := by
    have : (fun x : ℝ => psi (c * x)) = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * (((c * x : ℝ)) : ℂ)) := by
      funext x; rw [psi]
    rw [this]; fun_prop
  have hG : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℝ) = Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := by
    intro x; congr 1; ring
  have hint0 : Integrable (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x)) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq hb) ?_ (ae_of_all _ fun x => ?_)
    · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul hpsi_cont).aestronglyMeasurable
    · rw [norm_mul, hpsi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG]
  have hint1 : Integrable (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x)) := by
    refine Integrable.mono' ((integrable_exp_neg_mul_sq hb).add (integrable_mul_exp_neg_mul_sq hb).norm) ?_ (ae_of_all _ fun x => ?_)
    · exact (((Complex.continuous_ofReal.comp (by fun_prop)).mul (by fun_prop)).mul hpsi_cont).aestronglyMeasurable
    · simp only [Pi.add_apply]
      rw [norm_mul, norm_mul, hpsi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hG,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      have h1x : ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ≤ 1 + |x| := by
        calc ‖(1 : ℂ) + Complex.I * (x : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (x : ℂ)‖ := norm_add_le _ _
          _ = 1 + |x| := by rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hE : 0 ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := Real.exp_nonneg _
      calc Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * ‖(1 : ℂ) + Complex.I * (x : ℂ)‖
          ≤ Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) * (1 + |x|) := mul_le_mul_of_nonneg_left h1x hE
        _ = Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) + |x| * Real.exp (-(Real.pi / y₁ ^ 2) * x ^ 2) := by ring
  simp_rw [hsplit]
  rw [integral_add (hint1.const_mul _) (hint0.const_mul _), integral_const_mul, integral_const_mul,
    x_moment c hy₁, x_moment0 c hy₁]
  have h1 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁
  push_cast
  field_simp
  ring

end Ws25K7majx

theorem solution
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by
  obtain ⟨σ₁, h₁⟩ := LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
    ν₁ ν₂ a₁ a₂ W hWc hW D a ha 1 0
  obtain ⟨σ₂, h₂⟩ := LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
    ν₁ ν₂ a₁ a₂ W hWc hW D a ha 0 1
  refine ⟨max σ₁ σ₂, fun s hs y₁ hy₁ y₂ hy₂ => ?_⟩
  have I₁ := h₁ s (lt_of_le_of_lt (le_max_left _ _) hs) y₁ hy₁ y₂ hy₂
  have I₂ := h₂ s (lt_of_le_of_lt (le_max_right _ _) hs) y₁ hy₁ y₂ hy₂
  set T : ℝ → ℂ := fun t => W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) *
    (((t ^ 2)⁻¹ : ℝ) : ℂ) with hT
  set Φ : ℝ → ℝ → ℂ := fun x t =>
    ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * ((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
      ArchR.psi (a * t * x)) * T t with hΦ
  have hΦint : Integrable (Function.uncurry Φ) ((volume : Measure ℝ).prod volume) := by
    refine ((I₁.const_mul (((1 / y₁ + 1 / y₂ : ℝ) : ℂ))).add (I₂.const_mul (((1 / y₁ : ℝ)) : ℂ))).congr
      (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, hΦ, hT, Pi.add_apply]
    push_cast
    ring
  set C : ℂ := ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
      (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ)) * ((|y₁ * y₂| : ℝ) : ℂ) *
        (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
        ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
          Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
      ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) with hC
  have hE : ∀ x : ℝ, ((Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) =
      ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ)) * (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) := by
    intro x; rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 1; congr 1; field_simp; ring
  have hinner : ∀ x : ℝ,
      (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
        (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) = ∫ t : ℝ, ArchR.psi (a * t * x) * T t := by
    intro x; congr 1; funext t; simp only [hT]; ring
  have hL : ∀ x : ℝ,
      ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) = C * ∫ t : ℝ, Φ x t := by
    intro x
    rw [hinner x, hE x]
    have hΦx : (∫ t : ℝ, Φ x t) = ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        ((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) * ∫ t : ℝ, ArchR.psi (a * t * x) * T t := by
      rw [← integral_const_mul]; congr 1; funext t; simp only [hΦ]; ring
    rw [hΦx, hC]; ring
  have hxm : ∀ t : ℝ, (∫ x : ℝ, Φ x t) = ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) *
      (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ) * T t := by
    intro t
    rw [← Ws25K7majx.x_moment_major (a * t) hy₁ y₂, ← integral_mul_const]
  have hR : ∀ t : ℝ,
      (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) = C * ∫ x : ℝ, Φ x t := by
    intro t; rw [hxm t, hC, hT]; ring
  calc (∫ x : ℝ, ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ + 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))
      = ∫ x : ℝ, C * ∫ t : ℝ, Φ x t := by congr 1; funext x; exact hL x
    _ = C * ∫ x : ℝ, ∫ t : ℝ, Φ x t := integral_const_mul _ _
    _ = C * ∫ t : ℝ, ∫ x : ℝ, Φ x t := by rw [integral_integral_swap hΦint]
    _ = ∫ t : ℝ, C * ∫ x : ℝ, Φ x t := (integral_const_mul _ _).symm
    _ = ∫ t : ℝ, (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by congr 1; funext t; exact (hR t).symm

#print axioms solution

end
end S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_blockHarmonic_eq_integral_postGaussian_torusTriple (solution)
