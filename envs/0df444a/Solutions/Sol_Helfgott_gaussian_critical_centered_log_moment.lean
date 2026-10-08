-- Prove2me | solution 1 for Helfgott.gaussian_critical_centered_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T00:39:58.810272+00:00
-- url     : https://prove2.me/submissions/a3ec30d6-8ac1-4586-a168-474374eabf33

import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

section
open MeasureTheory Set Real Complex

namespace Helfgott

lemma mellin_log_integrable (σ : ℝ) (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ)) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  have hd : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) univ u := by
    intro u hu
    simpa only [mul_neg, mul_one] using
      (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt)
  have him : Real.exp ∘ Neg.neg '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
      Set.image_univ, Real.range_exp]
  have hinj : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent, ← him, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hd hinj] at hf
  have he (u : ℝ) : |(-Real.exp (-u))| •
      ((Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) • f (Real.exp (-u))) =
      Real.exp (-σ * u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _), ← smul_assoc]
    change ((Real.exp (-u) : ℂ) *
      (Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1)) * f (Real.exp (-u)) =
      (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))
    congr 1
    calc
      (Real.exp (-u) : ℂ) * (Real.exp (-u) : ℂ) ^ ((σ : ℂ) - 1) =
          (Real.exp (-u) : ℂ) ^ (1 + ((σ : ℂ) - 1)) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
          Complex.cpow_one]
      _ = (Real.exp (-σ * u) : ℂ) := by
        have hs : (1 : ℂ) + ((σ : ℂ) - 1) = (σ : ℂ) := by ring
        rw [hs, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
          ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
          ← Complex.ofReal_mul, ← Complex.ofReal_exp]
        congr 2
        ring
  simpa only [IntegrableOn, Function.comp_def, he, Measure.restrict_univ] using hf


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace Helfgott

lemma exp_neg_mellin_convergent (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Complex.exp (-(t : ℂ))) s := by
  simpa only [MellinConvergent, Complex.GammaIntegral, smul_eq_mul, mul_comm,
    Complex.ofReal_exp, Complex.ofReal_neg] using Complex.GammaIntegral_convergent hs

lemma exp_neg_half_mellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) s
      ((2 : ℂ) ^ s * Complex.Gamma s) := by
  constructor
  · have h := (MellinConvergent.comp_mul_left
      (f := fun t : ℝ => Complex.exp (-(t : ℂ)))
      (s := s) (a := (1/2 : ℝ)) (by norm_num)).mpr
        (exp_neg_mellin_convergent s hs)
    convert h using 1
    ext t
    push_cast
    congr 1
    ring
  · unfold mellin
    simp only [smul_eq_mul]
    have he := Complex.integral_cpow_mul_exp_neg_mul_Ioi
      (a := s) (r := (1/2 : ℝ)) hs (by norm_num)
    convert he using 1
    · congr 1
      ext t
      push_cast
      congr 2
      ring
    · norm_num

theorem phi_hasMellin (s : ℂ) (hs : -2 < s.re) :
    HasMellin (fun t : ℝ => (phi t : ℂ)) s
      ((2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 1)) := by
  let z : ℂ := (s + 2) / 2
  have hz : 0 < z.re := by dsimp [z]; simp; linarith
  have h := exp_neg_half_mellin z hz
  have he : (fun t : ℝ => (phi t : ℂ)) =
      fun t : ℝ => (t : ℂ) ^ (2 : ℂ) * Complex.exp (-((t ^ (2 : ℝ) : ℝ) : ℂ) / 2) := by
    ext t
    simp [phi, Real.rpow_two, Complex.ofReal_exp, Complex.ofReal_div,
      Complex.ofReal_neg, Complex.ofReal_pow, Complex.cpow_ofNat]
  rw [he]
  constructor
  · change MellinConvergent (fun t : ℝ => (t : ℂ) ^ (2 : ℂ) •
        Complex.exp (-((t ^ (2 : ℝ) : ℝ) : ℂ) / 2)) s
    rw [MellinConvergent.cpow_smul]
    exact (MellinConvergent.comp_rpow
      (f := fun t : ℝ => Complex.exp (-(t : ℂ) / 2))
      (s := s+2) (a := (2 : ℝ)) (by norm_num)).mpr h.1
  · change mellin (fun t : ℝ => (t : ℂ) ^ (2 : ℂ) •
        Complex.exp (-((t ^ (2 : ℝ) : ℝ) : ℂ) / 2)) s = _
    rw [mellin_cpow_smul, mellin_comp_rpow
      (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) (s+2) (2 : ℝ)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [Complex.ofReal_ofNat]
    change (1/2 : ℝ) • mellin (fun t : ℝ => Complex.exp (-(t : ℂ) / 2)) z = _
    rw [h.2]
    have hez : z = s / 2 + 1 := by dsimp [z]; ring
    rw [hez, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    push_cast
    ring


end Helfgott
end

section
open MeasureTheory
open scoped FourierTransform

namespace Helfgott

theorem fourier_second_derivative_decay {f f₁ f₂ : ℝ → ℂ}
    (h₀ : Integrable f) (h₁ : Integrable f₁) (h₂ : Integrable f₂)
    (hd₀ : ∀ u, HasDerivAt f (f₁ u) u) (hd₁ : ∀ u, HasDerivAt f₁ (f₂ u) u)
    (ξ : ℝ) :
    (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ ≤ ∫ u : ℝ, ‖f₂ u‖ := by
  have he₀ : deriv f = f₁ := funext (fun u => (hd₀ u).deriv)
  have he₁ : deriv f₁ = f₂ := funext (fun u => (hd₁ u).deriv)
  have hf₀ := congrFun (Real.fourier_deriv h₀ (fun u => (hd₀ u).differentiableAt)
    (by rw [he₀]; exact h₁)) ξ
  rw [he₀] at hf₀
  have hf₁ := congrFun (Real.fourier_deriv h₁ (fun u => (hd₁ u).differentiableAt)
    (by rw [he₁]; exact h₂)) ξ
  rw [he₁] at hf₁
  have hidentity : 𝓕 f₂ ξ = ((2*Real.pi*Complex.I*(ξ : ℂ))^2)*𝓕 f ξ := by
    rw [hf₁,hf₀]
    simp only [smul_eq_mul,pow_two,mul_assoc]
  have hn : ‖𝓕 f₂ ξ‖ = (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ := by
    rw [hidentity,norm_mul,norm_pow]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos Real.pi_pos,Complex.norm_I,mul_one]
  rw [← hn,Real.fourier_eq]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (innerₗ ℝ) f₂ ξ

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def gaussianLogPhase (k ω u : ℝ) : ℂ :=
  Complex.exp (-(k : ℂ) * (u : ℂ) - (Real.exp (-u) : ℂ)^2 / 2 +
    Complex.I * (ω : ℂ) * (Real.exp (-u) : ℂ))

lemma gaussianLogPhase_norm (k ω u : ℝ) :
    ‖gaussianLogPhase k ω u‖ = Real.exp (-k*u - (Real.exp (-u))^2/2) := by
  rw [gaussianLogPhase, Complex.norm_exp, ← Complex.ofReal_pow]
  congr 1
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.div_ofNat_re, mul_zero, zero_mul, sub_zero, add_zero]

lemma gaussianLogPhase_integrable (k ω : ℝ) (hk : 0 < k) :
    Integrable (gaussianLogPhase k ω) := by
  have hm := (phi_hasMellin ((k-2 : ℝ) : ℂ) (by simp; linarith)).1
  have hi := mellin_log_integrable (k-2) (fun t : ℝ => (phi t : ℂ)) hm
  apply hi.norm.mono' (by
    apply Continuous.aestronglyMeasurable
    unfold gaussianLogPhase
    fun_prop)
  filter_upwards [] with u
  rw [gaussianLogPhase_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold phi; positivity)]
  unfold phi
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

lemma gaussianLogPhase_shift (k ω u : ℝ) :
    gaussianLogPhase (k+1) ω u = (Real.exp (-u) : ℂ) * gaussianLogPhase k ω u := by
  unfold gaussianLogPhase
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma gaussianLogPhase_shift_two (k ω u : ℝ) :
    gaussianLogPhase (k+2) ω u = (Real.exp (-u) : ℂ)^2 * gaussianLogPhase k ω u := by
  have hs : k+2 = (k+1)+1 := by ring
  rw [hs, gaussianLogPhase_shift, gaussianLogPhase_shift]
  ring

lemma gaussianLogPhase_hasDerivAt (k ω u : ℝ) :
    HasDerivAt (gaussianLogPhase k ω)
      (-(k : ℂ)*gaussianLogPhase k ω u + gaussianLogPhase (k+2) ω u -
        Complex.I*(ω : ℂ)*gaussianLogPhase (k+1) ω u) u := by
  have ht : HasDerivAt (fun v : ℝ => (Real.exp (-v) : ℂ))
      (-(Real.exp (-u) : ℂ)) u := by
    convert (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).ofReal_comp) using 1 <;>
      simp
  have he := (((hasDerivAt_id u).ofReal_comp.const_mul (-(k : ℂ))).sub
    ((ht.pow 2).div_const 2)).add (ht.const_mul (Complex.I*(ω : ℂ)))
  have hd := (Complex.hasDerivAt_exp _).comp u he
  change HasDerivAt (gaussianLogPhase k ω)
    (gaussianLogPhase k ω u *
      (-(k : ℂ)*1 - ((2 : ℂ)*(Real.exp (-u) : ℂ)^(2-1)*
        (-(Real.exp (-u) : ℂ)))/2 + (Complex.I*(ω : ℂ))*(-(Real.exp (-u) : ℂ)))) u at hd
  have hh :
      gaussianLogPhase k ω u *
        (-(k : ℂ)*1 - ((2 : ℂ)*(Real.exp (-u) : ℂ)^(2-1)*
          (-(Real.exp (-u) : ℂ)))/2 + (Complex.I*(ω : ℂ))*(-(Real.exp (-u) : ℂ))) =
      -(k : ℂ)*gaussianLogPhase k ω u + gaussianLogPhase (k+2) ω u -
        Complex.I*(ω : ℂ)*gaussianLogPhase (k+1) ω u := by
    rw [gaussianLogPhase_shift_two, gaussianLogPhase_shift]
    norm_num
    ring
  rw [hh] at hd
  exact hd

noncomputable def gaussianLogPhaseDeriv (k ω u : ℝ) : ℂ :=
  -(k : ℂ)*gaussianLogPhase k ω u + gaussianLogPhase (k+2) ω u -
    Complex.I*(ω : ℂ)*gaussianLogPhase (k+1) ω u

noncomputable def gaussianLogPhaseSecond (k ω u : ℝ) : ℂ :=
  -(k : ℂ)*gaussianLogPhaseDeriv k ω u + gaussianLogPhaseDeriv (k+2) ω u -
    Complex.I*(ω : ℂ)*gaussianLogPhaseDeriv (k+1) ω u

lemma gaussianLogPhaseDeriv_integrable (k ω : ℝ) (hk : 0 < k) :
    Integrable (gaussianLogPhaseDeriv k ω) := by
  exact (((gaussianLogPhase_integrable k ω hk).const_mul (-(k : ℂ))).add
    (gaussianLogPhase_integrable (k+2) ω (by linarith))).sub
    ((gaussianLogPhase_integrable (k+1) ω (by linarith)).const_mul (Complex.I*(ω : ℂ)))

lemma gaussianLogPhaseSecond_integrable (k ω : ℝ) (hk : 0 < k) :
    Integrable (gaussianLogPhaseSecond k ω) := by
  exact (((gaussianLogPhaseDeriv_integrable k ω hk).const_mul (-(k : ℂ))).add
    (gaussianLogPhaseDeriv_integrable (k+2) ω (by linarith))).sub
    ((gaussianLogPhaseDeriv_integrable (k+1) ω (by linarith)).const_mul (Complex.I*(ω : ℂ)))

lemma gaussianLogPhaseDeriv_hasDerivAt (k ω u : ℝ) :
    HasDerivAt (gaussianLogPhaseDeriv k ω) (gaussianLogPhaseSecond k ω u) u := by
  exact ((((gaussianLogPhase_hasDerivAt k ω u).const_mul (-(k : ℂ))).add
    (gaussianLogPhase_hasDerivAt (k+2) ω u)).sub
    ((gaussianLogPhase_hasDerivAt (k+1) ω u).const_mul (Complex.I*(ω : ℂ))))

lemma fourier_integrable_of_two_integrable_derivatives {f f₁ f₂ : ℝ → ℂ}
    (h₀ : Integrable f) (h₁ : Integrable f₁) (h₂ : Integrable f₂)
    (hd₀ : ∀ u, HasDerivAt f (f₁ u) u) (hd₁ : ∀ u, HasDerivAt f₁ (f₂ u) u) :
    Integrable (𝓕 f) := by
  have hc : Continuous (𝓕 f) := by
    have he : 𝓕 f = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f := by
      funext ξ
      rw [Real.fourier_eq]
      rfl
    rw [he]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2)) h₀
  let A := ∫ u : ℝ, ‖f u‖
  let C := (∫ u : ℝ, ‖f₂ u‖) / (4*Real.pi^2)
  have hb (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ A := by
    rw [Real.fourier_eq]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) f ξ
  have hd (ξ : ℝ) : ξ^2*‖𝓕 f ξ‖ ≤ C := by
    have h := fourier_second_derivative_decay h₀ h₁ h₂ hd₀ hd₁ ξ
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi^2)).mpr
    have he : (2*Real.pi*|ξ|)^2 * ‖𝓕 f ξ‖ =
        (ξ^2 * ‖𝓕 f ξ‖) * (4*Real.pi^2) := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    rw [he] at h
    exact h
  apply (integrable_inv_one_add_sq.const_mul (A+C)).mono' hc.aestronglyMeasurable
  filter_upwards [] with ξ
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+ξ^2)).mpr
  nlinarith [hb ξ,hd ξ]

lemma gaussianLogPhase_fourier_integrable (k ω : ℝ) (hk : 0 < k) :
    Integrable (𝓕 (gaussianLogPhase k ω)) :=
  fourier_integrable_of_two_integrable_derivatives
    (gaussianLogPhase_integrable k ω hk)
    (gaussianLogPhaseDeriv_integrable k ω hk)
    (gaussianLogPhaseSecond_integrable k ω hk)
    (gaussianLogPhase_hasDerivAt k ω)
    (gaussianLogPhaseDeriv_hasDerivAt k ω)

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

lemma integral_comp_exp_univ (g : ℝ → ℝ) :
    (∫ u : ℝ, Real.exp u*g (Real.exp u)) = ∫ t in Ioi (0 : ℝ), g t := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

lemma integrable_comp_exp_univ (g : ℝ → ℝ) :
    Integrable (fun u : ℝ => Real.exp u*g (Real.exp u)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have him : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
    rw [image_univ,Real.range_exp]
  rw [← him]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u _ v _ h => Real.exp_injective h) g
  simpa only [integrableOn_univ,abs_of_pos (Real.exp_pos _),smul_eq_mul] using h.symm

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

lemma phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*phi t) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (s := ((k+2 : ℕ) : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) (k+2); linarith : (-1 : ℝ) < ((k+2 : ℕ) : ℝ))
  convert! h using 1
  funext t
  rw [Real.rpow_natCast]
  unfold phi
  rw [pow_add]
  have he : -(1/2 : ℝ)*t^2 = -(t^2)/2 := by ring
  rw [he]
  ring

lemma gaussian_power_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*Real.exp (-(t^2)/2)) =
      (1/2 : ℝ)^(-(((k : ℝ)+1)/2))*(1/2)*Real.Gamma (((k : ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  simp only [neg_div] at h ⊢
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast,Real.rpow_two]
  congr 1 <;> ring

theorem phi_mass : (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 2
  norm_num only [Nat.cast_ofNat] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  have he : (1/2 : ℝ)^(-(3/2 : ℝ)) = 2*Real.sqrt 2 := by
    rw [show (-(3/2 : ℝ)) = -1+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  change (∫ t in Ioi (0 : ℝ), t^2*Real.exp (-(t^2)/2)) = _
  rw [h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), t*phi t) = 2 := by
  have h := gaussian_power_integral 3
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have he : (1/2 : ℝ)^(-(2 : ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),Real.rpow_two]
    norm_num
  have heq : (fun t : ℝ => t*phi t) = fun t => t^3*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num [hg,he]

theorem phi_second_moment : (∫ t in Ioi (0 : ℝ), t^2*phi t) =
    3*Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 4
  have hg : Real.Gamma (5/2 : ℝ) = (3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ) = 3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ) = 1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (1/2 : ℝ)^(-(5/2 : ℝ)) = 4*Real.sqrt 2 := by
    rw [show (-(5/2 : ℝ)) = -2+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_two,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  have heq : (fun t : ℝ => t^2*phi t) = fun t => t^4*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def phiPhase (ω t : ℝ) : ℂ :=
  (phi t : ℂ) * Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))

lemma phiPhase_continuous (ω : ℝ) : Continuous (phiPhase ω) := by
  unfold phiPhase phi
  fun_prop

lemma phiPhase_norm (ω t : ℝ) : ‖phiPhase ω t‖ = ‖(phi t : ℂ)‖ := by
  rw [phiPhase, norm_mul, Complex.norm_exp]
  have he : (Complex.I*(ω : ℂ)*(t : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [he, Real.exp_zero, mul_one]

lemma phiPhase_mellin_convergent (ω : ℝ) (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (phiPhase ω) s := by
  have hm := (phi_hasMellin s hs).1
  have hc : Continuous (fun t : ℝ => (phi t : ℂ)) := by unfold phi; fun_prop
  rw [MellinConvergent, mellin_convergent_iff_norm (Subset.refl _) measurableSet_Ioi
    ((phiPhase_continuous ω).aestronglyMeasurable.mono_measure Measure.restrict_le_self)]
  rw [MellinConvergent, mellin_convergent_iff_norm (Subset.refl _) measurableSet_Ioi
    (hc.aestronglyMeasurable.mono_measure Measure.restrict_le_self)] at hm
  simpa only [phiPhase_norm] using hm

lemma phiPhase_log_kernel (σ ω u : ℝ) :
    Real.exp (-σ*u) • phiPhase ω (Real.exp (-u)) = gaussianLogPhase (σ+2) ω u := by
  rw [gaussianLogPhase_shift_two]
  unfold phiPhase phi gaussianLogPhase
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  simp only [sub_eq_add_neg, neg_div, Complex.exp_add]
  ring_nf

theorem phiPhase_mellin_vertical_integrable (σ ω : ℝ) (hσ : -2 < σ) :
    Complex.VerticalIntegrable (mellin (phiPhase ω)) σ := by
  have hi := (gaussianLogPhase_fourier_integrable (σ+2) ω (by linarith)).comp_mul_right'
    (by positivity : (1 / (2*Real.pi) : ℝ) ≠ 0)
  have he (t : ℝ) : mellin (phiPhase ω) ((σ : ℂ) + (t : ℂ)*Complex.I) =
      𝓕 (gaussianLogPhase (σ+2) ω) ((1 / (2*Real.pi))*t) := by
    rw [mellin_eq_fourier]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, phiPhase_log_kernel]
    congr 1
    ring
  change Integrable (fun t : ℝ => mellin (phiPhase ω) ((σ : ℂ) + (t : ℂ)*Complex.I))
  simp_rw [he]
  convert hi using 1
  ext t
  congr 1
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def gaussianLogFirstBound (k W u : ℝ) : ℝ :=
  k*‖gaussianLogPhase k 0 u‖ + ‖gaussianLogPhase (k+2) 0 u‖ +
    W*‖gaussianLogPhase (k+1) 0 u‖

noncomputable def gaussianLogSecondBound (k W u : ℝ) : ℝ :=
  k*gaussianLogFirstBound k W u + gaussianLogFirstBound (k+2) W u +
    W*gaussianLogFirstBound (k+1) W u

lemma gaussianLogFirstBound_integrable (k W : ℝ) (hk : 0 < k) :
    Integrable (gaussianLogFirstBound k W) := by
  exact (((gaussianLogPhase_integrable k 0 hk).norm.const_mul k).add
    (gaussianLogPhase_integrable (k+2) 0 (by linarith)).norm).add
    ((gaussianLogPhase_integrable (k+1) 0 (by linarith)).norm.const_mul W)

lemma gaussianLogSecondBound_integrable (k W : ℝ) (hk : 0 < k) :
    Integrable (gaussianLogSecondBound k W) := by
  exact (((gaussianLogFirstBound_integrable k W hk).const_mul k).add
    (gaussianLogFirstBound_integrable (k+2) W (by linarith))).add
    ((gaussianLogFirstBound_integrable (k+1) W (by linarith)).const_mul W)

lemma gaussianLogPhaseDeriv_norm_bound (k ω W u : ℝ) (hk : 0 < k) (hW : |ω| ≤ W) :
    ‖gaussianLogPhaseDeriv k ω u‖ ≤ gaussianLogFirstBound k W u := by
  unfold gaussianLogPhaseDeriv gaussianLogFirstBound
  calc
    _ ≤ ‖-(k : ℂ)*gaussianLogPhase k ω u‖ + ‖gaussianLogPhase (k+2) ω u‖ +
        ‖Complex.I*(ω : ℂ)*gaussianLogPhase (k+1) ω u‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk, Complex.norm_I, one_mul, gaussianLogPhase_norm]
      gcongr

lemma gaussianLogPhaseSecond_norm_bound (k ω W u : ℝ) (hk : 0 < k) (hW : |ω| ≤ W) :
    ‖gaussianLogPhaseSecond k ω u‖ ≤ gaussianLogSecondBound k W u := by
  unfold gaussianLogPhaseSecond gaussianLogSecondBound
  calc
    _ ≤ ‖-(k : ℂ)*gaussianLogPhaseDeriv k ω u‖ + ‖gaussianLogPhaseDeriv (k+2) ω u‖ +
        ‖Complex.I*(ω : ℂ)*gaussianLogPhaseDeriv (k+1) ω u‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk, Complex.norm_I, one_mul]
      have hW0 : 0 ≤ W := (abs_nonneg ω).trans hW
      gcongr
      · exact gaussianLogPhaseDeriv_norm_bound k ω W u hk hW
      · exact gaussianLogPhaseDeriv_norm_bound (k+2) ω W u (by linarith) hW
      · exact gaussianLogPhaseDeriv_norm_bound (k+1) ω W u (by linarith) hW

lemma phiPhase_mellin_fourier (σ ω t : ℝ) :
    mellin (phiPhase ω) ((σ : ℂ) + (t : ℂ)*Complex.I) =
      𝓕 (gaussianLogPhase (σ+2) ω) (t/(2*Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add, phiPhase_log_kernel]

lemma phiPhase_mellin_uniform_bound (σ ω W t : ℝ) (hσ : -2 < σ) (hW : |ω| ≤ W) :
    (1+t^2)*‖mellin (phiPhase ω) ((σ : ℂ) + (t : ℂ)*Complex.I)‖ ≤
      (∫ u : ℝ, ‖gaussianLogPhase (σ+2) 0 u‖) +
        (∫ u : ℝ, gaussianLogSecondBound (σ+2) W u) := by
  have hk : 0 < σ+2 := by linarith
  rw [phiPhase_mellin_fourier]
  have hb : ‖𝓕 (gaussianLogPhase (σ+2) ω) (t/(2*Real.pi))‖ ≤
      ∫ u : ℝ, ‖gaussianLogPhase (σ+2) 0 u‖ := by
    rw [Real.fourier_eq]
    have h := VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (gaussianLogPhase (σ+2) ω) (t/(2*Real.pi))
    simpa only [gaussianLogPhase_norm, VectorFourier.fourierIntegral, innerₗ_apply_apply] using h
  have hd := fourier_second_derivative_decay
    (gaussianLogPhase_integrable (σ+2) ω hk)
    (gaussianLogPhaseDeriv_integrable (σ+2) ω hk)
    (gaussianLogPhaseSecond_integrable (σ+2) ω hk)
    (gaussianLogPhase_hasDerivAt (σ+2) ω)
    (gaussianLogPhaseDeriv_hasDerivAt (σ+2) ω) (t/(2*Real.pi))
  have he : (2*Real.pi*|t/(2*Real.pi)|)^2 = t^2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2*Real.pi)]
    field_simp
    exact sq_abs t
  rw [he] at hd
  have hi : (∫ u : ℝ, ‖gaussianLogPhaseSecond (σ+2) ω u‖) ≤
      ∫ u : ℝ, gaussianLogSecondBound (σ+2) W u :=
    integral_mono (gaussianLogPhaseSecond_integrable (σ+2) ω hk).norm
      (gaussianLogSecondBound_integrable (σ+2) W hk)
      (fun u => gaussianLogPhaseSecond_norm_bound (σ+2) ω W u hk hW)
  nlinarith

theorem phiPhase_mellin_joint_continuous (σ : ℝ) (hσ : -2 < σ) :
    Continuous (fun p : ℝ × ℝ => mellin (phiPhase p.1)
      ((σ : ℂ) + (p.2 : ℂ)*Complex.I)) := by
  unfold mellin
  apply continuous_of_dominated
    (bound := fun u : ℝ => ‖(u : ℂ)^((σ : ℂ)-1) * (phi u : ℂ)‖)
  · intro p
    have hm : Measurable (fun u : ℝ =>
        (u : ℂ)^(((σ : ℂ)+(p.2 : ℂ)*Complex.I)-1) • phiPhase p.1 u) := by
      have hc := (phiPhase_continuous p.1).measurable
      fun_prop
    exact hm.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_smul, phiPhase_norm, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_cpow_eq_rpow_re_of_pos hu]
    simp
  · exact (phi_hasMellin (σ : ℂ) (by simpa using hσ)).1.norm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    unfold phiPhase
    simp only [Complex.cpow_def_of_ne_zero hu0, smul_eq_mul]
    fun_prop

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Complex
open scoped FourierTransform ComplexInnerProductSpace

namespace Helfgott

lemma integrable_norm_sq_of_integrable_bounded (f : ℝ → ℂ) (hf : Integrable f)
    (C : ℝ) (hC : 0≤C) (hbound : ∀ x,‖f x‖≤C) :
    Integrable (fun x => ‖f x‖^2) := by
  refine (hf.norm.const_mul C).mono' (hf.aestronglyMeasurable.norm.pow 2) ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg (f x),hbound x]

lemma integral_inner_fourier_of_integrable (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ : ℝ,inner ℂ (𝓕 f ξ) (g ξ)) =
      (∫ x : ℝ,inner ℂ (f x) (𝓕⁻ g x)) := by
  have hh := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar
    (by fun_prop : Continuous (fun p : ℝ×ℝ => (innerₗ ℝ) p.1 p.2)) hf hg
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards [] with ξ
    rw [Real.fourier_eq]
    rfl
  · apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    simp only [Real.fourierInv_eq,VectorFourier.fourierIntegral,
      LinearMap.neg_apply,LinearMap.flip_apply,neg_neg]
    congr 1
    funext v
    congr 1
    simp [mul_comm]

theorem integral_norm_sq_fourier_of_integrable (f : ℝ → ℂ)
    (hc : Continuous f) (hf : Integrable f) (hft : Integrable (𝓕 f)) :
    (∫ ξ : ℝ,‖𝓕 f ξ‖^2)=(∫ x : ℝ,‖f x‖^2) := by
  have hh := integral_inner_fourier_of_integrable f (𝓕 f) hf hft
  rw [hc.fourierInv_fourier_eq hf hft] at hh
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using hh

lemma gaussianLogPhase_energy_phase_independent (k ω : ℝ) (hk : 0<k) :
    (∫ ξ : ℝ,‖𝓕 (gaussianLogPhase k ω) ξ‖^2) =
      (∫ u : ℝ,Real.exp (-2*k*u-(Real.exp (-u))^2)) := by
  rw [integral_norm_sq_fourier_of_integrable (gaussianLogPhase k ω)
    (by unfold gaussianLogPhase; fun_prop)
    (gaussianLogPhase_integrable k ω hk) (gaussianLogPhase_fourier_integrable k ω hk)]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [gaussianLogPhase_norm,← Real.exp_nat_mul]
  congr 1
  ring

lemma gaussian_log_squared_mass (k : ℝ) (hk : 0<k) :
    (∫ u : ℝ,Real.exp (-2*k*u-(Real.exp (-u))^2))=Real.Gamma k/2 := by
  let g : ℝ → ℝ := fun t => Real.exp (-t)*t^(k-1)
  have hlog := integral_comp_exp_univ g
  have he (v : ℝ) : Real.exp v*g (Real.exp v)=Real.exp (k*v-Real.exp v) := by
    dsimp [g]
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [he] at hlog
  rw [← Real.Gamma_eq_integral hk] at hlog
  have hscale := Measure.integral_comp_mul_left (fun v : ℝ => Real.exp (k*v-Real.exp v)) (-2)
  simp only [show |(-2 : ℝ)⁻¹|=(1/2 : ℝ) by norm_num,smul_eq_mul] at hscale
  have he' (u : ℝ) : Real.exp (-2*k*u-(Real.exp (-u))^2)=Real.exp (k*(-2*u)-Real.exp (-2*u)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  simp_rw [he']
  rw [hscale,hlog]
  ring

theorem gaussianLogPhase_fourier_energy (k ω : ℝ) (hk : 0<k) :
    (∫ ξ : ℝ,‖𝓕 (gaussianLogPhase k ω) ξ‖^2)=Real.Gamma k/2 := by
  rw [gaussianLogPhase_energy_phase_independent k ω hk,gaussian_log_squared_mass k hk]

theorem phiPhase_critical_mellin_energy (ω : ℝ) :
    (∫ t : ℝ,‖mellin (phiPhase ω) ((1/2 : ℂ)+(t : ℂ)*I)‖^2)=
      3*Real.pi*Real.sqrt Real.pi/4 := by
  let g : ℝ → ℝ := fun ξ => ‖𝓕 (gaussianLogPhase (5/2) ω) ξ‖^2
  have hm (t : ℝ) :
      ‖mellin (phiPhase ω) ((1/2 : ℂ)+(t : ℂ)*I)‖^2=g ((1/(2*Real.pi))*t) := by
    have he := phiPhase_mellin_fourier (1/2) ω t
    norm_num at he
    rw [he]
    dsimp [g]
    congr 2
    ring
  simp_rw [hm]
  rw [Measure.integral_comp_mul_left]
  have hg : Real.Gamma (5/2 : ℝ)=(3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ)=3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ)=1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (∫ ξ : ℝ,g ξ)=Real.Gamma (5/2 : ℝ)/2 := gaussianLogPhase_fourier_energy _ _ (by norm_num)
  rw [he,hg]
  simp only [one_div,inv_inv,abs_of_pos (by positivity : (0 : ℝ)<2*Real.pi),smul_eq_mul]
  ring

theorem actual_gaussian_phase_critical_mellin_energy (ω : ℝ) :
    let G : ℝ → ℝ := fun t =>
      ‖mellin (fun u : ℝ => (phi u : ℂ)*Complex.exp (I*(ω : ℂ)*(u : ℂ)))
        ((1/2 : ℂ)+(t : ℂ)*I)‖^2
    Integrable G ∧ (∫ t : ℝ,G t)=3*Real.pi*Real.sqrt Real.pi/4 := by
  dsimp only
  have he := phiPhase_critical_mellin_energy ω
  refine ⟨?_,he⟩
  by_contra hn
  have hz := integral_undef hn
  have hz' := he.symm.trans hz
  have hp : (0 : ℝ)<3*Real.pi*Real.sqrt Real.pi/4 := by positivity
  linarith


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set Complex

namespace Helfgott

lemma real_sq_le_exp_add_exp_neg_sub_two (t : ℝ) :
    t^2≤Real.exp t+Real.exp (-t)-2 := by
  have hh := Real.self_le_sinh_iff.mpr (show 0≤|t|/2 by positivity)
  have hs : 0≤Real.sinh (|t|/2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hsq := (sq_le_sq₀ (by positivity : 0≤|t|/2) hs).mpr hh
  have hc := Real.cosh_two_mul (|t|/2)
  have hident := Real.cosh_sq_sub_sinh_sq (|t|/2)
  rw [show 2*(|t|/2)=|t| by ring,Real.cosh_abs,Real.cosh_eq] at hc
  nlinarith [sq_abs t]

lemma gaussian_log_squared_mass_integrable (k : ℝ) (hk : 0<k) :
    Integrable (fun u : ℝ => Real.exp (-2*k*u-(Real.exp (-u))^2)) := by
  refine (gaussianLogPhase_integrable (2*k) 0 (by positivity)).norm.mono'
    (by fun_prop) (ae_of_all _ (fun u => ?_))
  rw [Real.norm_of_nonneg (Real.exp_nonneg _),gaussianLogPhase_norm]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.exp (-u))]

lemma gaussian_centered_log_squared_mass (c : ℝ) :
    let F : ℝ → ℝ := fun u => (u+c)^2*Real.exp (-5*u-(Real.exp (-u))^2)
    Integrable F ∧ (∫ u : ℝ,F u)≤
      Real.exp c/2+Real.exp (-c)-3*Real.sqrt Real.pi/4 := by
  dsimp only
  let A : ℝ → ℝ := fun u => Real.exp c*Real.exp (-4*u-(Real.exp (-u))^2)
  let B : ℝ → ℝ := fun u => Real.exp (-c)*Real.exp (-6*u-(Real.exp (-u))^2)
  let C : ℝ → ℝ := fun u => 2*Real.exp (-5*u-(Real.exp (-u))^2)
  have hA : Integrable A := by
    dsimp [A]
    convert (gaussian_log_squared_mass_integrable 2 (by norm_num)).const_mul (Real.exp c) using 1
    congr 1; funext u; congr 2; ring
  have hB : Integrable B := by
    dsimp [B]
    convert (gaussian_log_squared_mass_integrable 3 (by norm_num)).const_mul (Real.exp (-c)) using 1
    congr 1; funext u; congr 2; ring
  have hC : Integrable C := by
    dsimp [C]
    convert (gaussian_log_squared_mass_integrable (5/2) (by norm_num)).const_mul 2 using 1
    congr 1; funext u; congr 2; ring
  have hb (u : ℝ) : (u+c)^2*Real.exp (-5*u-(Real.exp (-u))^2)≤A u+B u-C u := by
    have hh := mul_le_mul_of_nonneg_right (real_sq_le_exp_add_exp_neg_sub_two (u+c))
      (Real.exp_nonneg (-5*u-(Real.exp (-u))^2))
    have he : (Real.exp (u+c)+Real.exp (-(u+c))-2)*Real.exp (-5*u-(Real.exp (-u))^2)=A u+B u-C u := by
      dsimp [A,B,C]
      rw [sub_mul,add_mul]
      simp_rw [← Real.exp_add]
      congr 1
      · congr 1 <;> congr 1 <;> ring
    rwa [he] at hh
  have hi : Integrable (fun u : ℝ => (u+c)^2*Real.exp (-5*u-(Real.exp (-u))^2)) := by
    refine ((hA.add hB).sub hC).mono' (by fun_prop) (ae_of_all _ (fun u => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    exact hb u
  refine ⟨hi,?_⟩
  have hm := integral_mono hi ((hA.add hB).sub hC) hb
  have hg2 : Real.Gamma (2 : ℝ)=1 := by
    rw [show (2 : ℝ)=1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have hg3 : Real.Gamma (3 : ℝ)=2 := by
    rw [show (3 : ℝ)=2+1 by norm_num,Real.Gamma_add_one (by norm_num),hg2]
    norm_num
  have hg5 : Real.Gamma (5/2 : ℝ)=3*Real.sqrt Real.pi/4 := by
    rw [show (5/2 : ℝ)=3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ)=1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have heA : (∫ u : ℝ,A u)=Real.exp c/2 := by
    dsimp [A]
    rw [integral_const_mul]
    have he := gaussian_log_squared_mass 2 (by norm_num)
    norm_num only at he
    rw [he,hg2]
    ring
  have heB : (∫ u : ℝ,B u)=Real.exp (-c) := by
    dsimp [B]
    rw [integral_const_mul]
    have he := gaussian_log_squared_mass 3 (by norm_num)
    norm_num only at he
    rw [he,hg3]
    ring
  have heC : (∫ u : ℝ,C u)=3*Real.sqrt Real.pi/4 := by
    dsimp [C]
    rw [integral_const_mul]
    have he := gaussian_log_squared_mass (5/2) (by norm_num)
    norm_num only at he
    rw [he,hg5]
    ring
  change (∫ u : ℝ,(u+c)^2*Real.exp (-5*u-(Real.exp (-u))^2))≤
    (∫ u : ℝ,(A u+B u)-C u) at hm
  rw [integral_sub (f := fun u => A u+B u) (g := C) (hA.add hB) hC] at hm
  change (∫ u : ℝ,(u+c)^2*Real.exp (-5*u-(Real.exp (-u))^2))≤
    (∫ u : ℝ,A u+B u)-(∫ u : ℝ,C u) at hm
  rw [integral_add hA hB,heA,heB,heC] at hm
  exact hm

 theorem gaussian_critical_centered_log_moment :
    let F : ℝ → ℝ := fun u => (u+Real.log (Real.sqrt 2))^2*
      Real.exp (-5*u-(Real.exp (-u))^2)
    Integrable F ∧ (∫ u : ℝ,F u)≤Real.sqrt 2-3*Real.sqrt Real.pi/4 := by
  have hh := gaussian_centered_log_squared_mass (Real.log (Real.sqrt 2))
  rw [Real.exp_log (by positivity : 0<Real.sqrt 2),Real.exp_neg,
    Real.exp_log (by positivity : 0<Real.sqrt 2)] at hh
  have hs : (Real.sqrt 2)⁻¹=Real.sqrt 2/2 := by
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
    field_simp
    nlinarith
  rw [hs] at hh
  convert hh using 1 <;> ring

end Helfgott
end

open Helfgott MeasureTheory Set Complex

theorem solution :
    let F : ℝ → ℝ := fun u => (u+Real.log (Real.sqrt 2))^2*
      Real.exp (-5*u-(Real.exp (-u))^2)
    Integrable F ∧ (∫ u : ℝ,F u)≤Real.sqrt 2-3*Real.sqrt Real.pi/4 := Helfgott.gaussian_critical_centered_log_moment 

#print axioms solution
