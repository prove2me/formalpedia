-- Prove2me | solution 1 for Helfgott.etaStar_additive_phase_prime_LFunction_mellin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T10:04:15.813422+00:00
-- url     : https://prove2.me/submissions/9c1769e0-6cd6-4a73-b7ad-d68ce55215ec

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
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

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
open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_inner_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (w c : ℝ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t/w)*c/w) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t*w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn,div_eq_mul_inv,mul_assoc] using (hh.mul_const c).mul_const w⁻¹

lemma mellin_inner_integral (f : ℝ → ℝ) (w c : ℝ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t/w)*c/w) = c*(∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul,inv_inv,smul_eq_mul]
  field_simp

theorem mellin_integrable_mass (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) (hgi : IntegrableOn g (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (mellinConv f g) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), f t)*(∫ t in Ioi (0 : ℝ), g t) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t/w)*g w/w‖ ∂μ) =ᵐ[μ]
          fun w => g w*(∫ t, f t ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hnorm : (∫ t, ‖f (t/w)*g w/w‖ ∂μ) = ∫ t, f (t/w)*g w/w ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hfn _ (div_pos ht hw)) (hgn _ hw)) hw.le)
        rw [hnorm]
        exact mellin_inner_integral f w (g w) hw
      apply (hgi.mul_const (∫ t, f t ∂μ)).congr
      exact heq.symm
  constructor
  · exact hp.integral_prod_right
  unfold mellinConv
  change (∫ t, ∫ w, f (t/w)*g w/w ∂μ ∂μ) = _
  rw [← integral_integral_swap hp]
  have heq : (∫ w, ∫ t, f (t/w)*g w/w ∂μ ∂μ) =
      ∫ w, g w*(∫ t, f t ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact mellin_inner_integral f w (g w) hw
  rw [heq,integral_mul_const]
  exact mul_comm _ _

lemma mellin_moment_identity (f g : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    t^k*mellinConv f g t =
      mellinConv (fun t => t^k*f t) (fun w => w^k*g w) t := by
  unfold mellinConv
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [div_pow]
  have hn : w ≠ 0 := hw.ne'
  field_simp

theorem mellin_moment (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) (hfi : IntegrableOn (fun t => t^k*f t) (Ioi (0 : ℝ)))
    (hgi : IntegrableOn (fun t => t^k*g t) (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (fun t => t^k*mellinConv f g t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), t^k*f t)*(∫ t in Ioi (0 : ℝ), t^k*g t) := by
  simp_rw [mellin_moment_identity]
  apply mellin_integrable_mass _ _ ((continuous_id.pow k).mul hf) ((continuous_id.pow k).mul hg)
    hfi hgi
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hfn t ht)
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hgn t ht)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace Helfgott

lemma complex_mellin_inner_integrable (f : ℝ → ℂ)
    (hf : IntegrableOn f (Ioi (0 : ℝ))) (w : ℝ) (c : ℂ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t / w) * c / (w : ℂ)) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t * w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn, div_eq_mul_inv, mul_assoc] using
    (hh.mul_const c).mul_const (w : ℂ)⁻¹

lemma complex_mellin_inner_integral (f : ℝ → ℂ) (w : ℝ) (c : ℂ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t / w) * c / (w : ℂ)) =
      c * (∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul, inv_inv, Complex.real_smul]
  have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
  field_simp

theorem complex_mellin_convolution_integral (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (hgi : IntegrableOn g (Ioi (0 : ℝ))) :
    IntegrableOn (fun t : ℝ => ∫ w in Ioi (0 : ℝ), f (t / w) * g w / (w : ℂ))
      (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), f (t / w) * g w / (w : ℂ)) =
      (∫ t in Ioi (0 : ℝ), f t) * (∫ w in Ioi (0 : ℝ), g w) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2 / z.1) * g z.1 / (z.1 : ℂ)) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2 / z.1) * g z.1 / (z.1 : ℂ)) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact complex_mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t / w) * g w / (w : ℂ)‖ ∂μ) =ᵐ[μ]
          fun w => ‖g w‖ * (∫ t, ‖f t‖ ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        simp_rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
        exact mellin_inner_integral (fun t => ‖f t‖) w ‖g w‖ hw
      exact (hgi.norm.mul_const (∫ t, ‖f t‖ ∂μ)).congr heq.symm
  constructor
  · exact hp.integral_prod_right
  · change (∫ t, ∫ w, f (t / w) * g w / (w : ℂ) ∂μ ∂μ) = _
    rw [← integral_integral_swap hp]
    have heq : (∫ w, ∫ t, f (t / w) * g w / (w : ℂ) ∂μ ∂μ) =
        ∫ w, g w * (∫ t, f t ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact complex_mellin_inner_integral f w (g w) hw
    rw [heq, integral_mul_const]
    exact mul_comm _ _

theorem real_mellin_convolution_hasMellin (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (s : ℂ)
    (hfi : MellinConvergent (fun t : ℝ => (f t : ℂ)) s)
    (hgi : MellinConvergent (fun t : ℝ => (g t : ℂ)) s) :
    HasMellin (fun t : ℝ => (mellinConv f g t : ℂ)) s
      (mellin (fun t : ℝ => (f t : ℂ)) s *
        mellin (fun t : ℝ => (g t : ℂ)) s) := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (f t : ℂ)
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (g t : ℂ)
  have hFm : Measurable F := by dsimp [F]; fun_prop
  have hGm : Measurable G := by dsimp [G]; fun_prop
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := hfi
  have hG : IntegrableOn G (Ioi (0 : ℝ)) := hgi
  have h := complex_mellin_convolution_integral F G hFm hGm hF hG
  have he (t : ℝ) (ht : 0 < t) :
      (t : ℂ) ^ (s - 1) * (mellinConv f g t : ℂ) =
        ∫ w in Ioi (0 : ℝ), F (t / w) * G w / (w : ℂ) := by
    unfold mellinConv
    have hof : (∫ w in Ioi (0 : ℝ), ((f (t / w) * g w / w : ℝ) : ℂ)) =
        ((∫ w in Ioi (0 : ℝ), f (t / w) * g w / w : ℝ) : ℂ) := integral_ofReal
    rw [← hof, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp [F, G]
    push_cast
    rw [Complex.div_cpow_ofReal_nonneg ht.le hw.le]
    have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    have hwp : (w : ℂ) ^ (s - 1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    field_simp
  constructor
  · change IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * (mellinConv f g t : ℂ)) (Ioi (0 : ℝ))
    apply h.1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (he t ht).symm
  · unfold mellin
    simp only [smul_eq_mul]
    calc
      _ = ∫ t in Ioi (0 : ℝ), ∫ w in Ioi (0 : ℝ), F (t / w) * G w / (w : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact he t ht
      _ = _ := h.2


end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

lemma mellin_inverse_weight (F : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    w^(-2 : ℝ) * (F ((w^(-1 : ℝ))⁻¹)/(w^(-1 : ℝ))) = F w/w := by
  rw [Real.rpow_neg_one,inv_inv,Real.rpow_neg hw.le,Real.rpow_two]
  field_simp

theorem integral_mellin_inverse (F : ℝ → ℝ) :
    (∫ w in Ioi (0 : ℝ), F w/w) = ∫ w in Ioi (0 : ℝ), F w⁻¹/w := by
  have h := integral_comp_rpow_Ioi (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [abs_neg,abs_one,neg_sub,one_add_one_eq_two,smul_eq_mul,one_mul] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

theorem integrable_mellin_inverse (F : ℝ → ℝ) :
    IntegrableOn (fun w : ℝ => F w/w) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun w : ℝ => F w⁻¹/w) (Ioi (0 : ℝ)) := by
  have h := integrableOn_Ioi_comp_rpow_iff' (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [neg_sub,one_add_one_eq_two,smul_eq_mul] at h
  rw [← h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace Helfgott

lemma additivePhase_norm (ω t : ℝ) :
    ‖Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

lemma complex_mellin_product_joint_integrable (f g : ℝ → ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ)))
    (hgi : IntegrableOn g (Ioi (0 : ℝ))) :
    Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/(z.1 : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/(z.1 : ℂ)) := by fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact complex_mellin_inner_integrable f hfi w (g w) hw
  · have he : (fun w : ℝ => ∫ t in Ioi (0 : ℝ),
        ‖f (t/w)*g w/(w : ℂ)‖) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun w => ‖g w‖*(∫ t in Ioi (0 : ℝ), ‖f t‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      simp_rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
      exact mellin_inner_integral (fun t => ‖f t‖) w ‖g w‖ hw
    exact (hgi.norm.mul_const (∫ t in Ioi (0 : ℝ), ‖f t‖)).congr he.symm

lemma real_mellin_convolution_comm (f g : ℝ → ℝ) (T : ℝ) (hT : 0 < T) :
    mellinConv f g T = ∫ v in Ioi (0 : ℝ), f v*g (T/v)/v := by
  unfold mellinConv
  rw [integral_mellin_inverse (fun w => f (T/w)*g w)]
  let G : ℝ → ℝ := fun v => f v*g (T/v)/v
  have he : (∫ w in Ioi (0 : ℝ), f (T/w⁻¹)*g w⁻¹/w) =
      T*(∫ w in Ioi (0 : ℝ), G (T*w)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    dsimp [G]
    congr 1 <;> field_simp
  rw [he, integral_comp_mul_left_Ioi G 0 hT]
  simp only [mul_zero, smul_eq_mul]
  field_simp
  rfl

theorem mellin_gaussian_phase_convolution (f : ℝ → ℝ) (hf : Measurable f)
    (s : ℂ) (hs : -2 < s.re)
    (hfi : MellinConvergent (fun t : ℝ => (f t : ℂ)) s) (ω : ℝ) :
    mellin (fun t : ℝ => (mellinConv f phi t : ℂ)*
      Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))) s =
      ∫ w in Ioi (0 : ℝ), (w : ℂ)^(s-1)*(f w : ℂ)*mellin (phiPhase (ω*w)) s := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℂ := fun t => (t : ℂ)^(s-1)*(phi t : ℂ)
  let G : ℝ → ℂ := fun w => (w : ℂ)^(s-1)*(f w : ℂ)
  let J : ℝ × ℝ → ℂ := fun z =>
    F (z.2/z.1)*G z.1/(z.1 : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(z.2 : ℂ))
  have hFm : Measurable F := by
    unfold F
    have hphi : Measurable phi := by unfold phi; fun_prop
    fun_prop
  have hGm : Measurable G := by unfold G; fun_prop
  have hm : Measurable J := by unfold J; fun_prop
  have hi : Integrable J (μ.prod μ) := by
    apply (complex_mellin_product_joint_integrable F G hFm hGm
      (phi_hasMellin s hs).1 hfi).norm.mono' hm.aestronglyMeasurable
    filter_upwards [] with z
    dsimp [J]
    rw [norm_mul, additivePhase_norm, mul_one]
  have he (t : ℝ) (ht : 0 < t) :
      (t : ℂ)^(s-1)*((mellinConv f phi t : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))) =
        ∫ w, J (w,t) ∂μ := by
    rw [real_mellin_convolution_comm f phi t ht]
    have hof : ((∫ w in Ioi (0 : ℝ), f w*phi (t/w)/w : ℝ) : ℂ) =
        ∫ w in Ioi (0 : ℝ), ((f w*phi (t/w)/w : ℝ) : ℂ) := integral_ofReal.symm
    rw [hof, ← integral_mul_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp [J,F,G]
    push_cast
    rw [Complex.div_cpow_ofReal_nonneg ht.le hw.le]
    have hw0 : (w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hw.ne'
    have hwp : (w : ℂ)^(s-1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    field_simp
  have ht (w : ℝ) (hw : 0 < w) :
      (∫ t, J (w,t) ∂μ) = G w*mellin (phiPhase (ω*w)) s := by
    have heq : (∫ t, J (w,t) ∂μ) =
        ∫ t in Ioi (0 : ℝ), ((t/w : ℝ) : ℂ)^(s-1)*
          phiPhase (ω*w) (t/w)*G w/(w : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      dsimp [J,F,phiPhase]
      have hex : Complex.I*(ω*w : ℝ)*((t/w : ℝ) : ℂ) =
          Complex.I*(ω : ℂ)*(t : ℂ) := by
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr hw.ne']
      rw [hex]
      ring
    rw [heq, complex_mellin_inner_integral
      (fun t : ℝ => (t : ℂ)^(s-1)*phiPhase (ω*w) t) w (G w) hw]
    rfl
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ = ∫ t, ∫ w, J (w,t) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact he t ht
    _ = ∫ w, ∫ t, J (w,t) ∂μ ∂μ := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact ht w hw

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
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators Interval

namespace Helfgott

lemma cpow_log_primitive_hasDeriv (s : ℂ) (hs : s ≠ 0) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ =>
      (y : ℂ) ^ s * ((Real.log y : ℂ) * s - 1) / s ^ 2)
      ((t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) t := by
  have hd := ((hasDerivAt_ofReal_cpow_const ht.ne' hs).mul
    (((Real.hasDerivAt_log ht.ne').ofReal_comp.mul_const s).sub_const 1)).div_const (s ^ 2)
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * (t : ℂ) := by
    calc
      _ = (t : ℂ) ^ ((s - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
  have he : (s * (t : ℂ) ^ (s - 1) * ((Real.log t : ℂ) * s - 1) +
      (t : ℂ) ^ s * ((t⁻¹ : ℝ) * s)) / s ^ 2 =
      (t : ℂ) ^ (s - 1) * (Real.log t : ℂ) := by
    rw [hp]
    push_cast
    field_simp
    ring
  rw [he] at hd
  exact hd

lemma integral_cpow_log_positive (s : ℂ) (hs : s ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) =
      (b : ℂ) ^ s * ((Real.log b : ℂ) * s - 1) / s ^ 2 -
      (a : ℂ) ^ s * ((Real.log a : ℂ) * s - 1) / s ^ 2 := by
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t :=
    (lt_min ha hb).trans_le ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => cpow_log_primitive_hasDeriv s hs t (hp t ht))
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht0 : t ≠ 0 := (hp t ht).ne'
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).mul
    (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht0))).continuousWithinAt

lemma etaTwo_mellin_convergent (s : ℂ) :
    MellinConvergent (fun t : ℝ => (etaTwo t : ℂ)) s := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)
  have hc : ContinuousOn F (Icc (1/4 : ℝ) 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).mul
      (Complex.continuous_ofReal.comp etaTwo_continuous).continuousAt).continuousWithinAt
  have hi : IntegrableOn F (Icc (1/4 : ℝ) 1) := hc.integrableOn_Icc
  have hzero (t : ℝ) (ht : t ∉ Icc (1/4 : ℝ) 1) : F t = 0 := by
    simp [F, etaTwo_eq_zero_of_not_mem t ht]
  have he : (Icc (1/4 : ℝ) 1).indicator F = F := by
    ext t
    by_cases ht : t ∈ Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht F
    · rw [Set.indicator_of_notMem ht, hzero t ht]
  have hall : Integrable F := by
    rw [← he]
    exact hi.integrable_indicator measurableSet_Icc
  exact hall.integrableOn

lemma etaTwo_mellin_eq_interval (s : ℂ) :
    mellin (fun t : ℝ => (etaTwo t : ℂ)) s =
      ∫ t : ℝ in (1/4 : ℝ)..1, (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc (1/4 : ℝ) 1)]
    · rw [intervalIntegral.integral_of_le (by norm_num : (1/4 : ℝ) ≤ 1),
        integral_Icc_eq_integral_Ioc]
    · intro t ht
      simp only [etaTwo_eq_zero_of_not_mem t ht, Complex.ofReal_zero, mul_zero]
  · intro t ht
    have ht0 : ¬0<t := ht
    simp [etaTwo, ht0]

theorem etaTwo_mellin_formula (s : ℂ) (hs : s ≠ 0) :
    mellin (fun t : ℝ => (etaTwo t : ℂ)) s =
      4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) (Ioi (0 : ℝ)) := by
    intro t ht
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).mul
      (Complex.continuous_ofReal.comp etaTwo_continuous).continuousAt).continuousWithinAt
  have hi (a b : ℝ) (ha : 0<a) (hb : 0<b) :
      IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) volume a b := by
    apply (hc.mono ?_).intervalIntegrable
    intro t ht
    exact (lt_min ha hb).trans_le ht.1
  rw [etaTwo_mellin_eq_interval,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi (1/4) (1/2) (by norm_num) (by norm_num))
      (hi (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t : ℝ in (1/4 : ℝ)..(1/2),
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) =
      4 * ((Real.log 4 : ℂ) * (∫ t : ℝ in (1/4 : ℝ)..(1/2), (t : ℂ) ^ (s - 1)) +
        (∫ t : ℝ in (1/4 : ℝ)..(1/2), (t : ℂ) ^ (s - 1) * (Real.log t : ℂ))) := by
    have hi1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s-1)) volume (1/4) (1/2) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hp : 0<t := (lt_min (by norm_num : (0 : ℝ)<1/4)
        (by norm_num : (0 : ℝ)<1/2)).trans_le ht.1
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne')).continuousWithinAt
    have hi2 : IntervalIntegrable (fun t : ℝ =>
        (t : ℂ) ^ (s-1) * (Real.log t : ℂ)) volume (1/4) (1/2) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hp : 0<t := by norm_num at ht ⊢; linarith [ht.1]
      exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne')).mul
        (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hp.ne'))).continuousWithinAt
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi1.const_mul _) hi2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)] at ht
    rw [etaTwo_eq_lower t ht, Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    push_cast
    ring
  have hhi : (∫ t : ℝ in (1/2 : ℝ)..1,
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) =
      -4 * (∫ t : ℝ in (1/2 : ℝ)..1, (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    rw [etaTwo_eq_upper t ht]
    push_cast
    ring
  rw [hlo, hhi, integral_cpow_log_positive s hs (1/4) (1/2) (by norm_num) (by norm_num),
    integral_cpow_log_positive s hs (1/2) 1 (by norm_num) (by norm_num),
    integral_cpow (r := s-1) (Or.inr ⟨by intro h; apply hs; linear_combination h,
      by norm_num [Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)]⟩)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -2 * Real.log 2 := by rw [one_div, Real.log_inv, h4]; ring
  have hp2 : (((1/2 : ℝ) : ℂ) ^ s) = (2 : ℂ) ^ (-s) := by
    rw [one_div, Complex.ofReal_inv]
    rw [Complex.inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2), Complex.cpow_neg]
    norm_num
  have hp4 : (((1/4 : ℝ) : ℂ) ^ s) = ((2 : ℂ) ^ (-s)) ^ 2 := by
    have he : (1/4 : ℝ) = (1/2 : ℝ)*(1/2) := by norm_num
    rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), hp2]
    ring
  rw [sub_add_cancel, h4, hhalf, hquarter, Real.log_one, Complex.ofReal_one,
    Complex.one_cpow, hp2, hp4]
  push_cast
  field_simp
  ring

lemma etaTwo_mellin_vertical_bound (σ t : ℝ) (hσ : 0 < σ) :
    ‖mellin (fun u : ℝ => (etaTwo u : ℂ))
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * (1 + (2 : ℝ) ^ (-σ)) ^ 2 / (σ ^ 2 + t ^ 2) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [s] at hr
    linarith
  have hn : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [s, Complex.normSq]
    ring
  have hp : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-σ) := by
    simpa [s] using (Complex.norm_cpow_eq_rpow_re_of_pos
      (x := (2 : ℝ)) (y := -s) (by norm_num))
  have hb : ‖1 - (2 : ℂ) ^ (-s)‖ ≤ 1 + (2 : ℝ) ^ (-σ) := by
    simpa [hp] using norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-s))
  rw [etaTwo_mellin_formula s hs, norm_div, norm_mul, norm_pow, norm_pow, hn]
  norm_num only [Complex.norm_ofNat]
  gcongr

lemma etaTwo_mellin_vertical_integrable (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (etaTwo u : ℂ))) σ := by
  let C : ℝ := 4 * (1 + (2 : ℝ) ^ (-σ)) ^ 2
  have hs (t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hc : Continuous (fun t : ℝ =>
      mellin (fun u : ℝ => (etaTwo u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    simp_rw [etaTwo_mellin_formula _ (hs _)]
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact pow_ne_zero 2 (hs t)
  apply (integrable_inv_one_add_sq.const_mul (C * (1 + σ⁻¹ ^ 2))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < σ ^ 2 + t ^ 2 := by positivity
  have hinv : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by field_simp
  have hcompare : 1 + t ^ 2 ≤ (σ ^ 2 + t ^ 2) * (1 + σ⁻¹ ^ 2) := by
    nlinarith [sq_nonneg σ, sq_nonneg (t * σ⁻¹)]
  calc
    _ ≤ C / (σ ^ 2 + t ^ 2) := etaTwo_mellin_vertical_bound σ t hσ
    _ ≤ (C * (1 + σ⁻¹ ^ 2)) * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ)<1+t^2)).mpr
      have hC : 0≤C := by dsimp [C]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hcompare hC]


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators

namespace Helfgott

lemma etaStar_mellin_convolution (s : ℂ) (hs : -2 < s.re) :
    HasMellin (fun t : ℝ => (etaStar t : ℂ)) s
      ((49 : ℂ) ^ (-s) *
        (mellin (fun t : ℝ => (etaTwo t : ℂ)) s *
          mellin (fun t : ℝ => (phi t : ℂ)) s)) := by
  have h := real_mellin_convolution_hasMellin etaTwo phi etaTwo_continuous.measurable
    (by unfold phi; fun_prop) s (etaTwo_mellin_convergent s) (phi_hasMellin s hs).1
  constructor
  · exact (MellinConvergent.comp_mul_left
      (f := fun t : ℝ => (mellinConv etaTwo phi t : ℂ))
      (s := s) (a := (49 : ℝ)) (by norm_num)).mpr h.1
  · change mellin (fun t : ℝ => (mellinConv etaTwo phi (49*t) : ℂ)) s = _
    rw [mellin_comp_mul_left (fun t : ℝ => (mellinConv etaTwo phi t : ℂ))
      s (by norm_num : (0 : ℝ)<49), h.2]
    norm_num

theorem etaStar_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (etaStar t : ℂ)) s
      ((49 : ℂ) ^ (-s) *
        (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
        ((2 : ℂ) ^ (s / 2) * Complex.Gamma (s / 2 + 1))) := by
  have hs0 : s ≠ 0 := by intro he; simpa [he] using hs
  have h := etaStar_mellin_convolution s (by linarith)
  rw [etaTwo_mellin_formula s hs0, (phi_hasMellin s (by linarith)).2] at h
  simpa only [mul_assoc] using h

lemma phi_div_integrable : IntegrableOn (fun w : ℝ => phi w / w) (Ioi (0 : ℝ)) := by
  have h := (phi_hasMellin 0 (by norm_num)).1
  change IntegrableOn (fun w : ℝ => (w : ℂ) ^ ((0 : ℂ) - 1) * (phi w : ℂ))
    (Ioi (0 : ℝ)) at h
  have hco : IntegrableOn (fun w : ℝ => ((phi w / w : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
    apply h.congr
    filter_upwards [] with w
    simp only [zero_sub, Complex.cpow_neg_one, Complex.ofReal_div]
    ring
  apply hco.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hphi : 0 ≤ phi w := by unfold phi; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg (div_nonneg hphi hw.le)]

theorem etaStar_continuous : Continuous etaStar := by
  unfold etaStar mellinConv
  apply continuous_of_dominated
    (bound := fun w : ℝ => (4 * Real.log 2) * (phi w / w))
  · intro t
    have hm : Measurable (fun w : ℝ => etaTwo ((49*t)/w) * phi w / w) := by
      have hphi : Measurable phi := by unfold phi; fun_prop
      have hTwo : Measurable etaTwo := etaTwo_continuous.measurable
      fun_prop
    exact hm.aestronglyMeasurable
  · intro t
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hphi : 0 ≤ phi w := by unfold phi; positivity
    have he : ‖etaTwo ((49*t)/w) * phi w / w‖ =
        etaTwo ((49*t)/w) * phi w / w :=
      Real.norm_of_nonneg (div_nonneg (mul_nonneg (etaTwo_nonneg _) hphi) hw.le)
    rw [he]
    have h := mul_le_mul_of_nonneg_right (etaTwo_le ((49*t)/w)) (div_nonneg hphi hw.le)
    simpa only [mul_div_assoc] using h
  · exact phi_div_integrable.const_mul (4 * Real.log 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hc : Continuous (fun t : ℝ => (49*t)/w) := by fun_prop
    exact ((etaTwo_continuous.comp hc).mul continuous_const).div_const w

lemma phi_mellin_vertical_bound (σ t : ℝ) :
    ‖mellin (fun u : ℝ => (phi u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∫ u in Ioi (0 : ℝ), ‖(u : ℂ) ^ ((σ : ℂ) - 1) * (phi u : ℂ)‖ := by
  unfold mellin
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ),
        ‖(u : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) * (phi u : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu,
        Complex.norm_cpow_eq_rpow_re_of_pos hu]
      simp

theorem etaStar_mellin_vertical_integrable (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (etaStar u : ℂ))) σ := by
  let A : ℝ := (49 : ℝ) ^ (-σ) *
    (∫ u in Ioi (0 : ℝ), ‖(u : ℂ) ^ ((σ : ℂ) - 1) * (phi u : ℂ)‖)
  have hc : Continuous (fun t : ℝ =>
      mellin (fun u : ℝ => (etaStar u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hs (t : ℝ) : -2 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using (show -2<σ by linarith)
    simp_rw [(etaStar_mellin_convolution _ (hs _)).2]
    have hpow : Continuous (fun t : ℝ => (49 : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
      simp only [Complex.cpow_def_of_ne_zero (by norm_num : (49 : ℂ) ≠ 0)]
      fun_prop
    have hTwo : Continuous (fun t : ℝ =>
        mellin (fun u : ℝ => (etaTwo u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      have hz (t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
        intro he; have hr := congrArg Complex.re he; simp at hr; linarith
      simp_rw [etaTwo_mellin_formula _ (hz _)]
      simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact (by fun_prop : Continuous (fun t : ℝ =>
        4 * (1 - Complex.exp (Complex.log 2 * -((σ : ℂ) + (t : ℂ)*Complex.I)))^2)).div
        (by fun_prop) (fun t => pow_ne_zero 2 (hz t))
    have hPhi : Continuous (fun t : ℝ =>
        mellin (fun u : ℝ => (phi u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
      simp_rw [(phi_hasMellin _ (hs _)).2]
      apply Continuous.mul
      · simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
        fun_prop
      · apply continuous_iff_continuousAt.mpr
        intro t
        have hd : ContinuousAt (fun u : ℝ =>
            ((σ : ℂ) + (u : ℂ) * Complex.I) / 2 + 1) t := by fun_prop
        have hg : ContinuousAt Complex.Gamma
            (((σ : ℂ) + (t : ℂ) * Complex.I) / 2 + 1) := by
          apply Complex.continuousAt_Gamma
          intro m he
          have hr := congrArg Complex.re he
          simp at hr
          have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        exact hg.comp (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * Complex.I) / 2 + 1) hd
    exact hpow.mul (hTwo.mul hPhi)
  apply ((etaTwo_mellin_vertical_integrable σ hσ).norm.const_mul A).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  rw [(etaStar_mellin_convolution _ (by simpa using (show -2<σ by linarith))).2]
  rw [norm_mul, norm_mul]
  have hn : ‖(49 : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ = (49 : ℝ) ^ (-σ) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (x := (49 : ℝ)) (by norm_num)
      (-((σ : ℂ) + (t : ℂ) * Complex.I))
  rw [hn]
  dsimp [A]
  calc
    _ ≤ (49 : ℝ) ^ (-σ) *
        (‖mellin (fun u : ℝ => (etaTwo u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
          (∫ u in Ioi (0 : ℝ), ‖(u : ℂ) ^ ((σ : ℂ) - 1) * (phi u : ℂ)‖)) := by
      gcongr
      exact phi_mellin_vertical_bound σ t
    _ = _ := by ring


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def etaStarPhase (ω t : ℝ) : ℂ :=
  (etaStar t : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))

lemma etaStarPhase_continuous (ω : ℝ) : Continuous (etaStarPhase ω) := by
  unfold etaStarPhase
  exact (Complex.continuous_ofReal.comp etaStar_continuous).mul (by fun_prop)

lemma etaStarPhase_norm (ω t : ℝ) : ‖etaStarPhase ω t‖ = ‖(etaStar t : ℂ)‖ := by
  rw [etaStarPhase, norm_mul, additivePhase_norm, mul_one]

lemma etaStarPhase_mellin_convergent (ω : ℝ) (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (etaStarPhase ω) s := by
  have hm := (etaStar_mellin_convolution s hs).1
  have hc : Continuous (fun t : ℝ => (etaStar t : ℂ)) :=
    Complex.continuous_ofReal.comp etaStar_continuous
  rw [MellinConvergent, mellin_convergent_iff_norm (Subset.refl _) measurableSet_Ioi
    ((etaStarPhase_continuous ω).aestronglyMeasurable.mono_measure Measure.restrict_le_self)]
  rw [MellinConvergent, mellin_convergent_iff_norm (Subset.refl _) measurableSet_Ioi
    (hc.aestronglyMeasurable.mono_measure Measure.restrict_le_self)] at hm
  simpa only [etaStarPhase_norm] using hm

theorem etaStarPhase_mellin_formula (ω : ℝ) (s : ℂ) (hs : -2 < s.re) :
    mellin (etaStarPhase ω) s = (49 : ℂ)^(-s)*
      ∫ w in Ioi (0 : ℝ), (w : ℂ)^(s-1)*(etaTwo w : ℂ)*
        mellin (phiPhase (ω*w/49)) s := by
  have he : etaStarPhase ω = fun t : ℝ =>
      ((fun v : ℝ => (mellinConv etaTwo phi v : ℂ)*
        Complex.exp (Complex.I*((ω/49 : ℝ) : ℂ)*(v : ℂ))) (49*t)) := by
    funext t
    unfold etaStarPhase etaStar
    congr 2
    push_cast
    ring
  rw [he, mellin_comp_mul_left
    (fun v : ℝ => (mellinConv etaTwo phi v : ℂ)*
      Complex.exp (Complex.I*((ω/49 : ℝ) : ℂ)*(v : ℂ))) s (by norm_num : (0 : ℝ)<49),
    mellin_gaussian_phase_convolution etaTwo etaTwo_continuous.measurable s hs
      (etaTwo_mellin_convergent s) (ω/49)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with w
  congr 3
  ring

lemma mellin_vertical_continuous_of_convergent (f : ℝ → ℂ) (σ : ℝ)
    (hf : MellinConvergent f (σ : ℂ)) :
    Continuous (fun t : ℝ => mellin f ((σ : ℂ)+(t : ℂ)*Complex.I)) := by
  let G : ℝ → ℂ := fun u => Real.exp (-σ*u) • f (Real.exp (-u))
  have hi : Integrable G := mellin_log_integrable σ f hf
  have hc : Continuous (𝓕 G) := by
    have he : 𝓕 G = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) G := by
      funext ξ
      rw [Real.fourier_eq]
      rfl
    rw [he]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2)) hi
  have he (t : ℝ) : mellin f ((σ : ℂ)+(t : ℂ)*Complex.I) = 𝓕 G (t/(2*Real.pi)) := by
    rw [mellin_eq_fourier]
    simp [G, Complex.mul_re, Complex.mul_im]
  simp_rw [he]
  exact hc.comp (by fun_prop)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set

namespace Helfgott

lemma etaTwo_real_mellin_weight_integrable (σ : ℝ) :
    IntegrableOn (fun w : ℝ => w^(σ-1)*etaTwo w) (Ioi (0 : ℝ)) := by
  have hi := (etaTwo_mellin_convergent (σ : ℂ)).norm
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hw,
    Complex.norm_real, Real.norm_of_nonneg (etaTwo_nonneg w)]
  simp

noncomputable def gaussianVerticalConstant (σ W : ℝ) : ℝ :=
  (∫ u : ℝ, ‖gaussianLogPhase (σ+2) 0 u‖) +
    (∫ u : ℝ, gaussianLogSecondBound (σ+2) W u)

lemma etaStarPhase_inner_vertical_bound (σ ω t w : ℝ) (hσ : -2 < σ) (hw : 0 < w) :
    ‖(w : ℂ)^(((σ : ℂ)+(t : ℂ)*Complex.I)-1)*(etaTwo w : ℂ)*
      mellin (phiPhase (ω*w/49)) ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      (w^(σ-1)*etaTwo w)*(gaussianVerticalConstant σ (|ω|/49)/(1+t^2)) := by
  by_cases hmem : w ∈ Icc (1/4 : ℝ) 1
  · have hω : |ω*w/49| ≤ |ω|/49 := by
      rw [abs_div, abs_mul, abs_of_pos hw]
      norm_num
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hmem.2 (abs_nonneg ω)
    have hb := phiPhase_mellin_uniform_bound σ (ω*w/49) (|ω|/49) t hσ hω
    have hbd : ‖mellin (phiPhase (ω*w/49)) ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤
        gaussianVerticalConstant σ (|ω|/49)/(1+t^2) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<1+t^2)).mpr
      dsimp [gaussianVerticalConstant]
      nlinarith [hb]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw,
      Complex.norm_real, Real.norm_of_nonneg (etaTwo_nonneg w)]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_le_mul_of_nonneg_left hbd (mul_nonneg (Real.rpow_nonneg hw.le _) (etaTwo_nonneg w))
  · rw [etaTwo_eq_zero_of_not_mem w hmem]
    simp

theorem etaStarPhase_mellin_vertical_bound (σ ω t : ℝ) (hσ : -2 < σ) :
    ‖mellin (etaStarPhase ω) ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      ((49 : ℝ)^(-σ)*(∫ w in Ioi (0 : ℝ), w^(σ-1)*etaTwo w)*
        gaussianVerticalConstant σ (|ω|/49))/(1+t^2) := by
  let s : ℂ := (σ : ℂ)+(t : ℂ)*Complex.I
  let F : ℝ → ℂ := fun w => (w : ℂ)^(s-1)*(etaTwo w : ℂ)*mellin (phiPhase (ω*w/49)) s
  let B : ℝ := gaussianVerticalConstant σ (|ω|/49)/(1+t^2)
  have hm : Measurable F := by
    have hp : Continuous (fun w : ℝ => (ω*w/49,t)) := by fun_prop
    have hc := (phiPhase_mellin_joint_continuous σ hσ).comp hp
    change Continuous (fun w : ℝ => mellin (phiPhase (ω*w/49)) s) at hc
    have hTwo : Measurable etaTwo := etaTwo_continuous.measurable
    have hprod : Measurable (fun w : ℝ => (w : ℂ)^(s-1)*(etaTwo w : ℂ)) := by fun_prop
    exact hprod.mul hc.measurable
  have hib : IntegrableOn (fun w : ℝ => (w^(σ-1)*etaTwo w)*B) (Ioi (0 : ℝ)) :=
    (etaTwo_real_mellin_weight_integrable σ).mul_const B
  have hbound : ∀ᵐ w : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ‖F w‖ ≤ (w^(σ-1)*etaTwo w)*B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact etaStarPhase_inner_vertical_bound σ ω t w hσ hw
  have hiF : IntegrableOn F (Ioi (0 : ℝ)) := hib.mono' hm.aestronglyMeasurable hbound
  have hi : (∫ w in Ioi (0 : ℝ), ‖F w‖) ≤ ∫ w in Ioi (0 : ℝ), (w^(σ-1)*etaTwo w)*B :=
    integral_mono_ae hiF.norm hib hbound
  have hnorm : ‖(49 : ℂ)^(-s)‖ = (49 : ℝ)^(-σ) := by
    change ‖((49 : ℝ) : ℂ)^(-s)‖ = (49 : ℝ)^(-σ)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ)<49)]
    simp [s]
  rw [etaStarPhase_mellin_formula ω s (by simpa [s] using hσ), norm_mul, hnorm]
  calc
    _ ≤ (49 : ℝ)^(-σ)*(∫ w in Ioi (0 : ℝ), ‖F w‖) := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ ≤ (49 : ℝ)^(-σ)*(∫ w in Ioi (0 : ℝ), (w^(σ-1)*etaTwo w)*B) := by
      gcongr
    _ = _ := by rw [integral_mul_const]; dsimp [B]; ring

theorem etaStarPhase_mellin_vertical_integrable (σ ω : ℝ) (hσ : -2 < σ) :
    Complex.VerticalIntegrable (mellin (etaStarPhase ω)) σ := by
  have hc := mellin_vertical_continuous_of_convergent (etaStarPhase ω) σ
    (etaStarPhase_mellin_convergent ω (σ : ℂ) (by simpa using hσ))
  let C := (49 : ℝ)^(-σ)*(∫ w in Ioi (0 : ℝ), w^(σ-1)*etaTwo w)*
    gaussianVerticalConstant σ (|ω|/49)
  change Integrable (fun t : ℝ => mellin (etaStarPhase ω) ((σ : ℂ)+(t : ℂ)*Complex.I))
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  simpa only [C, div_eq_mul_inv] using etaStarPhase_mellin_vertical_bound σ ω t hσ

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators LSeries.notation

namespace Helfgott

lemma vertical_cpow_norm (x : ℝ) (hx : 0 < x) (σ t : ℝ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma vertical_term_norm (c : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n‖ =
      ‖LSeries.term c (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

lemma positive_ratio_cpow_inverse (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((y / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy.le hx.le, Complex.cpow_neg,
    Complex.cpow_neg]
  simp [div_eq_mul_inv, mul_comm]

lemma vertical_term_continuous (c : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hn0]
    exact continuous_const.div (by fun_prop) (fun _ => Complex.exp_ne_zero _)

lemma vertical_cpow_continuous (x : ℝ) (hx : 0 < x) (σ : ℝ) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.cpow_def_of_ne_zero hx0]
  fun_prop

lemma mellin_series_term_integrable (c : ℕ → ℂ) (σ x : ℝ) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_term_continuous c σ n).mul (vertical_cpow_continuous x hx σ)).aestronglyMeasurable.mul hF.1
  apply (hF.norm.const_mul (‖LSeries.term c (σ : ℂ) n‖ * x ^ σ)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_term_norm, vertical_cpow_norm x hx]

lemma mellin_series_norm_integrals_summable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x) (f : ℝ → ℂ) :
    Summable (fun n => ∫ t : ℝ,
      ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
  simp_rw [norm_mul, vertical_term_norm, vertical_cpow_norm x hx,
    integral_const_mul]
  exact (hc.norm.mul_right (x ^ σ)).mul_right _

lemma mellin_series_integrable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hLm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    AEStronglyMeasurable.tsum (fun n => (vertical_term_continuous c σ n).aestronglyMeasurable)
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_cpow_continuous x hx σ).aestronglyMeasurable.mul hF.1).mul hLm
  have hb (t : ℝ) : ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∑' n, ‖LSeries.term c (σ : ℂ) n‖ := by
    have ht : Summable (fun n => ‖LSeries.term c
        ((σ : ℂ) + (t : ℂ) * Complex.I) n‖) :=
      hc.norm.congr (fun n => (vertical_term_norm c σ t n).symm)
    simpa only [LSeries, vertical_term_norm] using norm_tsum_le_tsum_norm ht
  apply (hF.norm.const_mul (x ^ σ * ∑' n, ‖LSeries.term c (σ : ℂ) n‖)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_cpow_norm x hx]
  calc
    x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (∑' n, ‖LSeries.term c (σ : ℂ) n‖) := by
      gcongr
      exact hb t
    _ = _ := by ring

theorem mellin_weighted_series_hasSum (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (σ x : ℝ) (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n => c n * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hi : ∀ n, Integrable (F n) := mellin_series_term_integrable c σ x hx f hF
  have hs : Summable (fun n => ∫ t, ‖F n t‖) :=
    mellin_series_norm_integrals_summable c σ x hc hx f
  have hterm (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t, F n t) =
      c n * f ((n : ℝ) / x) := by
    by_cases hn : n = 0
    · subst n
      simp [F, hc0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnratio : 0 < (n : ℝ) / x := div_pos hnpos hx
      have hinv := mellinInv_mellin_eq σ f hnratio hf hF
        (hcont.continuousAt (Ioi_mem_nhds hnratio))
      rw [← hinv]
      simp only [mellinInv, smul_eq_mul, Complex.real_smul]
      rw [← mul_assoc, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [F]
      rw [LSeries.term_of_ne_zero hn,
        positive_ratio_cpow_inverse x (n : ℝ) hx hnpos]
      push_cast
      ring
  have hsum := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hterm] at hsum
  have heq : (∫ t : ℝ, ∑' n, F n t) =
      ∫ t : ℝ, (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [F]
    rw [tsum_mul_right, tsum_mul_right]
    unfold LSeries
    ring
  rw [heq] at hsum
  exact hsum

theorem twisted_prime_mellin_hasSum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv (LSeries (fun n : ℕ => χ n)) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          LSeries (fun n : ℕ => χ n) ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have hs := mellin_weighted_series_hasSum
    (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  convert hs using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have he := χ.LSeries_twist_vonMangoldt_eq ht
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact congrArg
    (fun z : ℂ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) * z)
    he.symm

lemma twisted_prime_LFunction_identity (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv χ.LFunction s / χ.LFunction s := by
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact he

theorem twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
        χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
          χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have he (t : ℝ) := twisted_prime_LFunction_identity q χ
    ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  have hi := mellin_series_integrable
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ x hc hx f hF
  have hs := mellin_weighted_series_hasSum
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  simp_rw [he] at hi hs
  exact ⟨hi, hs⟩


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace Helfgott

theorem etaStar_additive_phase_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (etaStar u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((etaStar ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (etaStar u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := by
  exact twisted_prime_LFunction_mellin q χ σ x hσ hx (etaStarPhase ω)
    (etaStarPhase_mellin_convergent ω (σ : ℂ) (by simp; linarith))
    (etaStarPhase_mellin_vertical_integrable σ ω (by linarith))
    (etaStarPhase_continuous ω).continuousOn

end Helfgott
end

open MeasureTheory Set

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.etaStar u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((Helfgott.etaStar ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.etaStar u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := Helfgott.etaStar_additive_phase_prime_LFunction_mellin q χ σ x ω hσ hx

#print axioms solution
