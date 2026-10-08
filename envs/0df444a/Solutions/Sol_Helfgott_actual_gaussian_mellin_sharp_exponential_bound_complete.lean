-- Prove2me | solution 1 for Helfgott.actual_gaussian_mellin_sharp_exponential_bound_complete
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T01:16:20.871897+00:00
-- url     : https://prove2.me/submissions/fc291a13-6739-4288-9a7c-b7bc7ccc7d23

import Definitions.Def_Helfgott_GaussianSharpMellinBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Complex MeasureTheory Set Filter
open scoped Topology

namespace Helfgott

lemma horizontal_integral_eq_of_vertical_edges (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (h : ℝ)
    (h0 : Integrable (fun u : ℝ => f (u : ℂ)))
    (h1 : Integrable (fun u : ℝ => f ((u : ℂ)+(h : ℂ)*I)))
    (hp : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..h, f ((R : ℂ)+(y : ℂ)*I)) atTop (𝓝 0))
    (hm : Tendsto (fun R : ℝ => ∫ y : ℝ in 0..h, f ((-R : ℂ)+(y : ℂ)*I)) atTop (𝓝 0)) :
    (∫ u : ℝ,f (u : ℂ))=(∫ u : ℝ,f ((u : ℂ)+(h : ℂ)*I)) := by
  have hz (R : ℝ) := integral_boundary_rect_eq_zero_of_differentiableOn f
    ((-R : ℝ) : ℂ) ((R : ℂ)+(h : ℂ)*I) hf.differentiableOn
  simp only [ofReal_re,ofReal_im,add_re,add_im,mul_re,mul_im,I_re,I_im,
    mul_zero,zero_mul,mul_one,add_zero,zero_add] at hz
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have ht0 := intervalIntegral_tendsto_integral h0 hneg (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have ht1 := intervalIntegral_tendsto_integral h1 hneg (tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)
  have ht := ((ht0.sub ht1).add (hp.const_smul I)).sub (hm.const_smul I)
  simp only [smul_zero,add_zero,sub_zero] at ht
  have he : (fun R : ℝ => (∫ u : ℝ in -R..R,f (u : ℂ))-
      (∫ u : ℝ in -R..R,f ((u : ℂ)+(h : ℂ)*I))+
      I • (∫ y : ℝ in 0..h,f ((R : ℂ)+(y : ℂ)*I))-
      I • (∫ y : ℝ in 0..h,f ((-R : ℂ)+(y : ℂ)*I)))=(fun _ : ℝ => (0 : ℂ)) := by
    funext R
    simpa using hz R
  simp only [id_eq] at ht
  rw [he] at ht
  exact sub_eq_zero.mp (tendsto_nhds_unique ht tendsto_const_nhds)

end Helfgott
end

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
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set

namespace Helfgott

lemma gaussian_power_seven_integral :
    (∫ t in Ioi (0 : ℝ), t^7*Real.exp (-(t^2)/2)) = 48 := by
  rw [gaussian_power_integral]
  norm_num only [Nat.cast_ofNat]
  have hg : Real.Gamma (4 : ℝ)=6 := by
    norm_num
  norm_num [hg, Real.rpow_neg, Real.rpow_natCast]

lemma gaussian_log_eight_mass :
    (∫ u : ℝ, ‖gaussianLogPhase 8 0 u‖) = 48 := by
  have h := integral_comp_exp_univ (fun t : ℝ => t^7*Real.exp (-(t^2)/2))
  have he (u : ℝ) : Real.exp u*((Real.exp u)^7*Real.exp (-((Real.exp u)^2)/2)) =
      ‖gaussianLogPhase 8 0 (-u)‖ := by
    rw [gaussianLogPhase_norm]
    simp only [neg_neg]
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he] at h
  have hn := MeasureTheory.integral_neg_eq_self (fun u : ℝ => ‖gaussianLogPhase 8 0 u‖) volume
  rw [hn] at h
  rw [h, gaussian_power_seven_integral]

theorem gaussian_log_mass_le (k : ℝ) (hk0 : (1/2 : ℝ) ≤ k) (hk8 : k ≤ 8) :
    (∫ u : ℝ, ‖gaussianLogPhase k 0 u‖) ≤ 64 := by
  have hk : 0 < k := by linarith
  have hi := (gaussianLogPhase_integrable k 0 hk).norm
  have h8 := (gaussianLogPhase_integrable 8 0 (by norm_num)).norm
  have hl : (∫ u in Iic (0 : ℝ), ‖gaussianLogPhase k 0 u‖) ≤ 48 := by
    calc
      _ ≤ ∫ u in Iic (0 : ℝ), ‖gaussianLogPhase 8 0 u‖ := by
        apply setIntegral_mono_on hi.integrableOn h8.integrableOn measurableSet_Iic
        intro u hu
        simp only [gaussianLogPhase_norm]
        apply Real.exp_le_exp.mpr
        have hp : 0 ≤ (8-k)*(-u) := mul_nonneg (by linarith) (by simpa using hu)
        nlinarith
      _ ≤ ∫ u : ℝ, ‖gaussianLogPhase 8 0 u‖ :=
        setIntegral_le_integral h8 (ae_of_all _ (fun u => norm_nonneg _))
      _ = _ := gaussian_log_eight_mass
  have hr : (∫ u in Ioi (0 : ℝ), ‖gaussianLogPhase k 0 u‖) ≤ 2 := by
    have he := integrableOn_exp_mul_Ioi (a := -(1/2 : ℝ)) (by norm_num) 0
    calc
      _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-(1/2 : ℝ)*u) := by
        apply setIntegral_mono_on hi.integrableOn he measurableSet_Ioi
        intro u hu
        rw [gaussianLogPhase_norm]
        apply Real.exp_le_exp.mpr
        have hp : 0 ≤ (k-1/2)*u := mul_nonneg (by linarith) (le_of_lt hu)
        nlinarith [sq_nonneg (Real.exp (-u))]
      _ = _ := by rw [integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ)<0) 0]; norm_num
  have hs := intervalIntegral.integral_Iic_add_Ioi (hi.restrict (s := Iic 0))
    (hi.restrict (s := Ioi 0))
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform

namespace Helfgott

noncomputable def gaussianComplexLog (k ω t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((k : ℂ)+(t : ℂ)*I)*z-Complex.exp (-(2 : ℂ)*z)/2+
    I*(ω : ℂ)*Complex.exp (-z))

lemma gaussianComplexLog_differentiable (k ω t : ℝ) :
    Differentiable ℂ (gaussianComplexLog k ω t) := by unfold gaussianComplexLog; fun_prop

lemma gaussianComplexLog_norm (k ω t x y : ℝ) :
    ‖gaussianComplexLog k ω t ((x : ℂ)+(y : ℂ)*I)‖=
      Real.exp (-k*x+t*y-Real.cos (2*y)*(Real.exp (-x))^2/2+
        ω*Real.sin y*Real.exp (-x)) := by
  rw [gaussianComplexLog,Complex.norm_exp]
  congr 1
  simp only [sub_re,sub_im,add_re,add_im,mul_re,mul_im,neg_re,neg_im,ofReal_re,ofReal_im,I_re,I_im,
    re_ofNat,im_ofNat,div_ofNat_re,Complex.exp_re,Complex.exp_im,
    mul_zero,zero_mul,mul_one,zero_add,add_zero,sub_zero,zero_sub,
    Real.cos_neg,Real.sin_neg,neg_zero]
  rw [show -(2 : ℝ)*x=(2 : ℕ)*(-x) by ring,Real.exp_nat_mul,
    show -(2 : ℝ)*y=-(2*y) by ring,Real.cos_neg]
  ring

lemma gaussianComplexLog_real_axis (k ω t x : ℝ) :
    gaussianComplexLog k ω t (x : ℂ)=
      Complex.exp (-I*(t : ℂ)*(x : ℂ))*gaussianLogPhase k ω x := by
  rw [gaussianComplexLog,gaussianLogPhase,← Complex.exp_add,Complex.ofReal_exp,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma gaussianComplexLog_axis_integrable (k ω t : ℝ) (hk : 0<k) :
    Integrable (fun x : ℝ => gaussianComplexLog k ω t (x : ℂ)) := by
  refine (gaussianLogPhase_integrable k ω hk).norm.mono' ?_ ?_
  · exact (gaussianComplexLog_differentiable k ω t).continuous.comp continuous_ofReal |>.aestronglyMeasurable
  · filter_upwards [] with x
    have hh := gaussianComplexLog_norm k ω t x 0
    simpa [gaussianLogPhase_norm] using hh.le

lemma gaussianComplexLog_quarter_strip_majorant (k ω t x y θ : ℝ)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hy : |y|≤θ) :
    ‖gaussianComplexLog k ω t ((x : ℂ)+(y : ℂ)*I)‖≤
      Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2)*
        Real.exp (-k*x-(7/32 : ℝ)*(Real.exp (-x))^2) := by
  rw [gaussianComplexLog_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcos : (7/8 : ℝ)≤Real.cos (2*y) := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := 2*y)
    have hyq : y^2≤(1/4 : ℝ)^2 := by
      have hyy : |y|≤1/4 := hy.trans hθ
      have hh := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ)≤1/4)).mpr hyy
      simpa only [sq_abs] using hh
    nlinarith
  have hsin : |Real.sin y|≤θ := Real.abs_sin_le_abs.trans hy
  have hty : t*y≤|t| *θ := (le_abs_self _).trans (by rw [abs_mul]; gcongr)
  have hphase : ω*Real.sin y*Real.exp (-x)≤|ω| *θ*Real.exp (-x) := by
    have hh : ω*Real.sin y≤|ω| *θ := (le_abs_self _).trans (by rw [abs_mul]; gcongr)
    exact mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
  have hquad : |ω| *θ*Real.exp (-x)≤(7/32 : ℝ)*(Real.exp (-x))^2+(8/7 : ℝ)*ω^2*θ^2 := by
    nlinarith [sq_nonneg ((7 : ℝ)*Real.exp (-x)-16*|ω| *θ),sq_abs ω]
  have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Real.exp (-x)))
  nlinarith
lemma gaussianComplexLog_shifted_majorant (k ω t x y θ : ℝ)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hy : |y|≤θ) :
    ‖gaussianComplexLog k ω t ((x : ℂ)+(y : ℂ)*I)‖≤
      Real.exp (t*y+(8/7 : ℝ)*ω^2*θ^2)*
        Real.exp (-k*x-(7/32 : ℝ)*(Real.exp (-x))^2) := by
  rw [gaussianComplexLog_norm,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcos : (7/8 : ℝ)≤Real.cos (2*y) := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := 2*y)
    have hyq : y^2≤(1/4 : ℝ)^2 := by
      have hyy : |y|≤1/4 := hy.trans hθ
      have hh := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ)≤1/4)).mpr hyy
      simpa only [sq_abs] using hh
    nlinarith
  have hsin : |Real.sin y|≤θ := Real.abs_sin_le_abs.trans hy
  have hphase : ω*Real.sin y*Real.exp (-x)≤|ω| *θ*Real.exp (-x) := by
    have hh : ω*Real.sin y≤|ω| *θ := (le_abs_self _).trans (by rw [abs_mul]; gcongr)
    exact mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
  have hquad : |ω| *θ*Real.exp (-x)≤(7/32 : ℝ)*(Real.exp (-x))^2+(8/7 : ℝ)*ω^2*θ^2 := by
    nlinarith [sq_nonneg ((7 : ℝ)*Real.exp (-x)-16*|ω| *θ),sq_abs ω]
  have hh := mul_le_mul_of_nonneg_right hcos (sq_nonneg (Real.exp (-x)))
  nlinarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Complex MeasureTheory Set Filter
open scoped Topology

namespace Helfgott

noncomputable def gaussianQuarterLog (k u : ℝ) : ℝ :=
  Real.exp (-k*u-(Real.exp (-u))^2/8)

lemma gaussianQuarterLog_translation (k u : ℝ) :
    gaussianQuarterLog k u=Real.exp (k*Real.log 2)*‖gaussianLogPhase k 0 (u+Real.log 2)‖ := by
  rw [gaussianQuarterLog,gaussianLogPhase_norm,← Real.exp_add]
  have he : Real.exp (-(u+Real.log 2))=Real.exp (-u)/2 := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 2),Real.exp_log (by norm_num : (0 : ℝ)<2)]
    ring
  rw [he]
  congr 1
  ring

lemma gaussianQuarterLog_integrable (k : ℝ) (hk : 0<k) : Integrable (gaussianQuarterLog k) := by
  have hh := ((gaussianLogPhase_integrable k 0 hk).norm.comp_add_right (Real.log 2)).const_mul (Real.exp (k*Real.log 2))
  simpa only [← gaussianQuarterLog_translation] using hh

lemma gaussianQuarterLog_mass_le (k : ℝ) (hk0 : (1/2 : ℝ)≤k) (hk3 : k≤3) :
    (∫ u : ℝ,gaussianQuarterLog k u)≤512 := by
  have hh : Real.exp (k*Real.log 2)≤8 := by
    calc
      _≤Real.exp (3*Real.log 2) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk3 (Real.log_nonneg (by norm_num)))
      _=8 := by rw [show (3 : ℝ)=(3 : ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]; norm_num
  simp_rw [gaussianQuarterLog_translation]
  rw [integral_const_mul]
  have he := integral_add_right_eq_self (μ := volume) (fun u : ℝ => ‖gaussianLogPhase k 0 u‖) (Real.log 2)
  rw [he]
  have hm := gaussian_log_mass_le k hk0 (by linarith)
  exact (mul_le_mul hh hm (integral_nonneg fun u => norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

lemma gaussianQuarterLog_tendsto_atTop (k : ℝ) (hk : 0<k) :
    Tendsto (gaussianQuarterLog k) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-k*u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hk)).mpr tendsto_id)
  refine squeeze_zero (fun u => (Real.exp_pos _).le) (fun u => ?_) he
  rw [gaussianQuarterLog]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.exp (-u))]

lemma gaussianQuarterLog_tendsto_atBot (k : ℝ) :
    Tendsto (gaussianQuarterLog k) atBot (𝓝 0) := by
  have hh := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num : (0 : ℝ)<1/8) k
  rw [cocompact_eq_atBot_atTop] at hh
  have ht := (hh.mono_left (show (atTop : Filter ℝ)≤atBot ⊔ atTop from le_sup_right)).comp
    (Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
  convert ht using 1
  funext u
  dsimp only [Function.comp_apply]
  rw [gaussianQuarterLog,abs_of_pos (Real.exp_pos _),Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
  congr 1
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform

namespace Helfgott

lemma gaussianComplexLog_quarter_majorant (k ω t x y θ : ℝ)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hy : |y|≤θ) :
    ‖gaussianComplexLog k ω t ((x : ℂ)+(y : ℂ)*I)‖≤
      Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2)*gaussianQuarterLog k x := by
  refine (gaussianComplexLog_quarter_strip_majorant k ω t x y θ hθ0 hθ hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rw [gaussianQuarterLog]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.exp (-x))]

lemma gaussianComplexLog_shifted_quarter_majorant (k ω t x y θ : ℝ)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hy : |y|≤θ) :
    ‖gaussianComplexLog k ω t ((x : ℂ)+(y : ℂ)*I)‖≤
      Real.exp (t*y+(8/7 : ℝ)*ω^2*θ^2)*gaussianQuarterLog k x := by
  refine (gaussianComplexLog_shifted_majorant k ω t x y θ hθ0 hθ hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rw [gaussianQuarterLog]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.exp (-x))]

lemma gaussianComplexLog_shifted_integrable (k ω t h θ : ℝ) (hk : 0<k)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hh : |h|≤θ) :
    Integrable (fun x : ℝ => gaussianComplexLog k ω t ((x : ℂ)+(h : ℂ)*I)) := by
  have hb := (gaussianQuarterLog_integrable k hk).const_mul (Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2))
  refine hb.mono' ?_ (ae_of_all _ (fun x => gaussianComplexLog_quarter_majorant k ω t x h θ hθ0 hθ hh))
  exact (gaussianComplexLog_differentiable k ω t).continuous.comp
    (show Continuous (fun x : ℝ => (x : ℂ)+(h : ℂ)*I) by fun_prop) |>.aestronglyMeasurable

lemma gaussianComplexLog_vertical_integral_norm_bound (k ω t R h θ : ℝ)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hh : |h|≤θ) :
    ‖∫ y : ℝ in 0..h,gaussianComplexLog k ω t ((R : ℂ)+(y : ℂ)*I)‖≤
      Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2)*gaussianQuarterLog k R*|h| := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := h) (C := Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2)*gaussianQuarterLog k R)
    (f := fun y : ℝ => gaussianComplexLog k ω t ((R : ℂ)+(y : ℂ)*I)) (fun y hy => ?_)
  · simpa only [sub_zero] using hb
  · have hyy : |y|≤|h| := by
      have he := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
      simpa only [sub_zero] using he
    exact gaussianComplexLog_quarter_majorant k ω t R y θ hθ0 hθ (hyy.trans hh)

lemma gaussianComplexLog_horizontal_rotation (k ω t h θ : ℝ) (hk : 0<k)
    (hθ0 : 0≤θ) (hθ : θ≤1/4) (hh : |h|≤θ) :
    (∫ u : ℝ,gaussianComplexLog k ω t (u : ℂ))=
      (∫ u : ℝ,gaussianComplexLog k ω t ((u : ℂ)+(h : ℂ)*I)) := by
  apply horizontal_integral_eq_of_vertical_edges _ (gaussianComplexLog_differentiable k ω t) h
    (gaussianComplexLog_axis_integrable k ω t hk)
    (gaussianComplexLog_shifted_integrable k ω t h θ hk hθ0 hθ hh)
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht := ((gaussianQuarterLog_tendsto_atTop k hk).const_mul (Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2))).mul_const |h|
    simp only [mul_zero,zero_mul] at ht
    exact squeeze_zero (fun R => norm_nonneg _) (fun R => gaussianComplexLog_vertical_integral_norm_bound k ω t R h θ hθ0 hθ hh) ht
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht := (((gaussianQuarterLog_tendsto_atBot k).comp tendsto_neg_atTop_atBot).const_mul (Real.exp (|t| *θ+(8/7 : ℝ)*ω^2*θ^2))).mul_const |h|
    simp only [mul_zero,zero_mul] at ht
    exact squeeze_zero (fun R => norm_nonneg _) (fun R => by simpa using gaussianComplexLog_vertical_integral_norm_bound k ω t (-R) h θ hθ0 hθ hh) ht

lemma gaussianComplexLog_integral_exponential_bound (k ω t θ : ℝ)
    (hk0 : (1/2 : ℝ)≤k) (hk3 : k≤3) (hθ0 : 0≤θ) (hθ : θ≤1/4) :
    ‖∫ u : ℝ,gaussianComplexLog k ω t (u : ℂ)‖≤
      512*Real.exp (-θ*|t|+(8/7 : ℝ)*ω^2*θ^2) := by
  let h : ℝ := if 0≤t then -θ else θ
  have hh : |h|≤θ := by dsimp [h]; split <;> simp [abs_of_nonneg hθ0]
  have htw : t*h=-θ*|t| := by
    dsimp [h]
    split_ifs with ht
    · rw [abs_of_nonneg ht]; ring
    · rw [abs_of_neg (lt_of_not_ge ht)]; ring
  rw [gaussianComplexLog_horizontal_rotation k ω t h θ (by linarith) hθ0 hθ hh]
  have hf := gaussianComplexLog_shifted_integrable k ω t h θ (by linarith) hθ0 hθ hh
  have hb := (gaussianQuarterLog_integrable k (by linarith)).const_mul
    (Real.exp (t*h+(8/7 : ℝ)*ω^2*θ^2))
  have hn := integral_mono hf.norm hb (fun u => gaussianComplexLog_shifted_quarter_majorant k ω t u h θ hθ0 hθ hh)
  rw [integral_const_mul,htw] at hn
  exact (norm_integral_le_integral_norm _).trans (hn.trans (by
    have hm := gaussianQuarterLog_mass_le k hk0 hk3
    nlinarith [mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (-θ*|t|+(8/7 : ℝ)*ω^2*θ^2))]))

lemma phiPhase_mellin_complex_log_integral (σ ω t : ℝ) :
    mellin (phiPhase ω) ((σ : ℂ)+(t : ℂ)*I)=
      (∫ u : ℝ,gaussianComplexLog (σ+2) ω t (u : ℂ)) := by
  rw [phiPhase_mellin_fourier,Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with u
  rw [gaussianComplexLog_real_axis,smul_eq_mul]
  congr 1
  apply congrArg Complex.exp
  simp only [RCLike.inner_apply,conj_trivial]
  push_cast
  field_simp [Real.pi_ne_zero]


theorem phiPhase_mellin_exponential_bound (σ ω t θ : ℝ)
    (hσl : -(1/2 : ℝ)≤σ) (hσu : σ≤1) (hθ0 : 0≤θ) (hθ : θ≤1/4) :
    ‖mellin (phiPhase ω) ((σ : ℂ)+(t : ℂ)*I)‖≤
      512*Real.exp (-θ*|t|+(8/7 : ℝ)*ω^2*θ^2) := by
  rw [phiPhase_mellin_complex_log_integral]
  exact gaussianComplexLog_integral_exponential_bound (σ+2) ω t θ (by linarith) (by linarith) hθ0 hθ


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory Set Filter
open scoped Topology

namespace Helfgott

noncomputable def shiftedGaussianLog (k a b u : ℝ) : ℝ :=
  Real.exp (-k*u-a*(Real.exp (-u)-b)^2)

lemma shiftedGaussianLog_integrable (k a b : ℝ) (hk : 0<k) (ha : (2/5 : ℝ)≤a) :
    Integrable (shiftedGaussianLog k a b) := by
  have h0 : (0 : ℝ)≤a := by linarith
  refine ((gaussianQuarterLog_integrable k hk).const_mul (Real.exp (a*b^2))).mono'
    (by unfold shiftedGaussianLog; fun_prop) (ae_of_all _ (fun u => ?_))
  rw [shiftedGaussianLog,Real.norm_of_nonneg (Real.exp_nonneg _),gaussianQuarterLog,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_nonneg h0 (sq_nonneg (Real.exp (-u)-2*b))
  nlinarith [sq_nonneg (Real.exp (-u))]

lemma gaussian_first_half_moment (a : ℝ) (ha : 0<a) :
    (∫ r in Ioi (0 : ℝ),r*Real.exp (-a*r^2))=(2*a)⁻¹ := by
  have hh := integral_mul_cexp_neg_mul_sq (b := (a : ℂ)) (by simpa using ha)
  have he : (fun r : ℝ => (r : ℂ)*Complex.exp (-(a : ℂ)*(r : ℂ)^2))=
      (fun r : ℝ => ((r*Real.exp (-a*r^2) : ℝ) : ℂ)) := by
    funext r
    simp only [Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_neg,Complex.ofReal_pow]
  rw [he,integral_complex_ofReal] at hh
  have he' : (2*(a : ℂ))⁻¹=(((2*a)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [he'] at hh
  exact Complex.ofReal_injective hh

lemma gaussian_first_absolute_moment (a : ℝ) (ha : 0<a) :
    (∫ r : ℝ,|r| * Real.exp (-a*r^2))=a⁻¹ := by
  have hi : Integrable (fun r : ℝ => |r| * Real.exp (-a*r^2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq ha).norm
  have hright : (∫ r in Ioi (0 : ℝ),|r| * Real.exp (-a*r^2))=(2*a)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [abs_of_pos hr])]
    exact gaussian_first_half_moment a ha
  have hleft : (∫ r in Iic (0 : ℝ),|r| * Real.exp (-a*r^2))=(2*a)⁻¹ := by
    have he := integral_comp_neg_Ioi (0 : ℝ) (fun r : ℝ => |r| * Real.exp (-a*r^2))
    simp only [neg_zero,abs_neg,neg_sq] at he
    rw [← he]
    exact hright
  have hh := intervalIntegral.integral_Iic_add_Ioi (hi.restrict (s := Iic 0))
    (hi.restrict (s := Ioi 0))
  rw [hleft,hright] at hh
  rw [← hh]
  field_simp
  <;> norm_num

lemma shifted_gaussian_linear_mass (a b : ℝ) (ha : (2/5 : ℝ)≤a) :
    (∫ r : ℝ,(|r-b|+|b|)*Real.exp (-a*(r-b)^2))≤5/2+3*|b| := by
  have hap : 0<a := by linarith
  have hig := integrable_exp_neg_mul_sq hap
  have hif : Integrable (fun r : ℝ => |r| * Real.exp (-a*r^2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq hap).norm
  have hi := hif.add (hig.const_mul |b|)
  have he : (∫ r : ℝ,(|r-b|+|b|)*Real.exp (-a*(r-b)^2))=
      a⁻¹+|b| * Real.sqrt (Real.pi/a) := by
    have ht := integral_add_right_eq_self (μ := volume)
      (fun r : ℝ => (|r|+|b|)*Real.exp (-a*r^2)) (-b)
    simp only [← sub_eq_add_neg] at ht
    rw [ht]
    simp_rw [add_mul]
    rw [integral_add hif (hig.const_mul |b|),integral_const_mul,
      gaussian_first_absolute_moment a hap,integral_gaussian]
  have hs : Real.sqrt (Real.pi/a)≤3 := by
    have hr : Real.pi/a≤9 := (div_le_iff₀ hap).mpr (by nlinarith [Real.pi_lt_d2.le])
    exact (Real.sqrt_le_sqrt hr).trans_eq (by norm_num)
  have hinv : a⁻¹≤5/2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hap).mpr
    linarith
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg b)]

lemma shifted_gaussian_linear_integrable (a b : ℝ) (ha : 0<a) :
    Integrable (fun r : ℝ => (|r-b|+|b|)*Real.exp (-a*(r-b)^2)) := by
  have hif : Integrable (fun r : ℝ => |r| * Real.exp (-a*r^2)) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq ha).norm
  have hi := (hif.add ((integrable_exp_neg_mul_sq ha).const_mul |b|)).comp_add_right (-b)
  convert hi using 1
  funext r
  dsimp
  ring_nf

lemma shiftedGaussianLog_mass_bound (k a b : ℝ) (hk0 : (1/2 : ℝ)≤k) (hk2 : k≤2)
    (ha : (2/5 : ℝ)≤a) :
    (∫ u : ℝ,shiftedGaussianLog k a b u)≤5+3*|b| := by
  have hk : 0<k := by linarith
  have hap : 0<a := by linarith
  have hi := shiftedGaussianLog_integrable k a b hk ha
  have hright : (∫ u in Ioi (0 : ℝ),shiftedGaussianLog k a b u)≤2 := by
    have hie := integrableOn_exp_mul_Ioi (a := -(1/2 : ℝ)) (by norm_num) 0
    calc
      _≤∫ u in Ioi (0 : ℝ),Real.exp (-(1/2 : ℝ)*u) := by
        apply setIntegral_mono_on hi.integrableOn hie measurableSet_Ioi
        intro u hu
        rw [shiftedGaussianLog]
        apply Real.exp_le_exp.mpr
        have hs := mul_nonneg hap.le (sq_nonneg (Real.exp (-u)-b))
        nlinarith [mul_nonneg (show 0≤k-1/2 by linarith) hu.le]
      _=2 := by rw [integral_exp_mul_Ioi (by norm_num : -(1/2 : ℝ)<0) 0]; norm_num
  let g : ℝ → ℝ := fun r => r^(k-1)*Real.exp (-a*(r-b)^2)
  have hchange : (∫ u in Iic (0 : ℝ),shiftedGaussianLog k a b u)=∫ r in Ioi (1 : ℝ),g r := by
    have hn := integral_comp_neg_Ioi (0 : ℝ) (shiftedGaussianLog k a b)
    simp only [neg_zero] at hn
    rw [← hn]
    have he := integral_comp_exp_Ioi g 0
    simp only [Real.exp_zero,smul_eq_mul] at he
    rw [← he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [shiftedGaussianLog,g]
    rw [neg_neg,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    simp_rw [← Real.exp_add]
    congr 1
    ring
  have hg (r : ℝ) (hr : r ∈ Ioi (1 : ℝ)) : g r≤(|r-b|+|b|)*Real.exp (-a*(r-b)^2) := by
    have hr0 : 0<r := lt_trans (by norm_num : (0 : ℝ)<1) hr
    have hrp : r^(k-1)≤r := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr.le (show k-1≤1 by linarith)
    have hab : r≤|r-b|+|b| := by
      have hh := abs_add_le (r-b) b
      simpa only [sub_add_cancel,abs_of_pos hr0] using hh
    exact mul_le_mul_of_nonneg_right (hrp.trans hab) (Real.exp_nonneg _)
  have him := shifted_gaussian_linear_integrable a b hap
  have hig : IntegrableOn g (Ioi (1 : ℝ)) := him.integrableOn.mono' (by
    dsimp [g]; fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : 0≤r := le_trans (by norm_num : (0 : ℝ)≤1) hr.le
      rw [Real.norm_of_nonneg (by dsimp [g]; positivity)]
      exact hg r hr)
  have hleft : (∫ u in Iic (0 : ℝ),shiftedGaussianLog k a b u)≤5/2+3*|b| := by
    rw [hchange]
    calc
      _≤∫ r in Ioi (1 : ℝ),(|r-b|+|b|)*Real.exp (-a*(r-b)^2) :=
        setIntegral_mono_on hig him.integrableOn measurableSet_Ioi hg
      _≤∫ r : ℝ,(|r-b|+|b|)*Real.exp (-a*(r-b)^2) :=
        setIntegral_le_integral him (ae_of_all _ (fun r => by positivity))
      _≤_ := shifted_gaussian_linear_mass a b ha
  have hh := intervalIntegral.integral_Iic_add_Ioi (hi.restrict (s := Iic 0))
    (hi.restrict (s := Ioi 0))
  linarith

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex MeasureTheory Set

namespace Helfgott

lemma gaussianComplexLog_completed_square (k ω t u h : ℝ) (hc : Real.cos (2*h)≠0) :
    ‖gaussianComplexLog k ω t ((u : ℂ)+(h : ℂ)*I)‖=
      Real.exp (t*h+ω^2*(Real.sin h)^2/(2*Real.cos (2*h)))*
        shiftedGaussianLog k (Real.cos (2*h)/2) (ω*Real.sin h/Real.cos (2*h)) u := by
  rw [gaussianComplexLog_norm,shiftedGaussianLog,← Real.exp_add]
  congr 1
  generalize Real.cos (2*h)=c at hc ⊢
  field_simp [hc]
  <;> ring

theorem gaussianComplexLog_integral_sharp_bound (k ω t θ c : ℝ)
    (hk0 : (1/2 : ℝ)≤k) (hk2 : k≤2) (hθ0 : 0≤θ) (hθ : θ≤1/4)
    (hc : (4/5 : ℝ)≤c) (hcos : c≤Real.cos (2*θ)) :
    ‖∫ u : ℝ,gaussianComplexLog k ω t (u : ℂ)‖≤
      (5+3*|ω| *θ/c)*Real.exp (-θ*|t|+ω^2*θ^2/(2*c)) := by
  let h : ℝ := if 0≤t then -θ else θ
  have hh : |h|≤θ := by dsimp [h]; split <;> simp [abs_of_nonneg hθ0]
  have htw : t*h=-θ*|t| := by
    dsimp [h]
    split_ifs with ht
    · rw [abs_of_nonneg ht]; ring
    · rw [abs_of_neg (lt_of_not_ge ht)]; ring
  have hce : Real.cos (2*h)=Real.cos (2*θ) := by
    dsimp [h]
    split <;> simp only [mul_neg,Real.cos_neg]
  have hcp : 0<c := by linarith
  have hcosp : 0<Real.cos (2*h) := by rw [hce]; linarith
  have hca : (2/5 : ℝ)≤Real.cos (2*h)/2 := by rw [hce]; linarith
  have hsin : |Real.sin h|≤θ := Real.abs_sin_le_abs.trans hh
  have hs2 : (Real.sin h)^2≤θ^2 := by
    have ht := (sq_le_sq₀ (abs_nonneg _) hθ0).mpr hsin
    simpa only [sq_abs] using ht
  have hb : |ω*Real.sin h/Real.cos (2*h)|≤|ω| *θ/c := by
    rw [abs_div,abs_mul,abs_of_pos hcosp]
    exact div_le_div₀ (mul_nonneg (abs_nonneg ω) hθ0)
      (mul_le_mul_of_nonneg_left hsin (abs_nonneg ω)) hcp (by rw [hce]; exact hcos)
  have hpen : ω^2*(Real.sin h)^2/(2*Real.cos (2*h))≤ω^2*θ^2/(2*c) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hs2 (sq_nonneg ω))
      (by positivity) (by rw [hce]; linarith)
  rw [gaussianComplexLog_horizontal_rotation k ω t h θ (by linarith) hθ0 hθ hh]
  have hf := gaussianComplexLog_shifted_integrable k ω t h θ (by linarith) hθ0 hθ hh
  have hm := shiftedGaussianLog_mass_bound k (Real.cos (2*h)/2)
    (ω*Real.sin h/Real.cos (2*h)) hk0 hk2 hca
  have hi := shiftedGaussianLog_integrable k (Real.cos (2*h)/2)
    (ω*Real.sin h/Real.cos (2*h)) (by linarith) hca
  have he : (∫ u : ℝ,‖gaussianComplexLog k ω t ((u : ℂ)+(h : ℂ)*I)‖)=
      Real.exp (t*h+ω^2*(Real.sin h)^2/(2*Real.cos (2*h)))*
        (∫ u : ℝ,shiftedGaussianLog k (Real.cos (2*h)/2) (ω*Real.sin h/Real.cos (2*h)) u) := by
    simp_rw [gaussianComplexLog_completed_square k ω t _ h hcosp.ne']
    rw [integral_const_mul]
  have hm0 : 0≤∫ u : ℝ,shiftedGaussianLog k (Real.cos (2*h)/2)
      (ω*Real.sin h/Real.cos (2*h)) u := integral_nonneg (fun u => Real.exp_nonneg _)
  calc
    _≤∫ u : ℝ,‖gaussianComplexLog k ω t ((u : ℂ)+(h : ℂ)*I)‖ := norm_integral_le_integral_norm _
    _≤(5+3*|ω| *θ/c)*Real.exp (-θ*|t|+ω^2*θ^2/(2*c)) := by
      rw [he,htw]
      have hmb : (∫ u : ℝ,shiftedGaussianLog k (Real.cos (2*h)/2)
          (ω*Real.sin h/Real.cos (2*h)) u)≤5+3*|ω| *θ/c := by
        calc
          _≤5+3*|ω*Real.sin h/Real.cos (2*h)| := hm
          _≤5+3*(|ω| *θ/c) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by norm_num))
          _=_ := by ring
      have hem := Real.exp_le_exp.mpr (add_le_add (le_refl (-θ*|t|)) hpen)
      exact (mul_le_mul hem hmb hm0 (Real.exp_nonneg _)).trans_eq (mul_comm _ _)

end Helfgott
end

section
set_option autoImplicit false
open Complex MeasureTheory

namespace Helfgott

theorem actual_gaussian_mellin_sharp_exponential_bound (σ ω t θ c : ℝ)
    (hσl : -(3/2 : ℝ)≤σ) (hσu : σ≤0) (hθ0 : 0≤θ) (hθ : θ≤1/4)
    (hc : (4/5 : ℝ)≤c) (hcos : c≤Real.cos (2*θ)) :
    ‖mellin (fun u : ℝ => (phi u : ℂ)*Complex.exp (I*(ω : ℂ)*(u : ℂ)))
      ((σ : ℂ)+(t : ℂ)*I)‖≤
      (5+3*|ω| *θ/c)*Real.exp (-θ*|t|+ω^2*θ^2/(2*c)) := by
  change ‖mellin (phiPhase ω) ((σ : ℂ)+(t : ℂ)*I)‖≤_
  rw [phiPhase_mellin_complex_log_integral]
  exact gaussianComplexLog_integral_sharp_bound (σ+2) ω t θ c
    (by linarith) (by linarith) hθ0 hθ hc hcos

end Helfgott
end

theorem solution : Helfgott.GaussianSharpMellinBound := by
  exact Helfgott.actual_gaussian_mellin_sharp_exponential_bound

#print axioms solution
