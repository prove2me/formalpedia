-- Prove2me | solution 1 for Helfgott.phi_additive_phase_prime_LFunction_mellin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T09:48:20.449973+00:00
-- url     : https://prove2.me/submissions/712e6538-feef-49b1-9ab3-3232d0fec241

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
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

theorem phi_additive_phase_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (phi u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((phi ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (phi u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := by
  exact twisted_prime_LFunction_mellin q χ σ x hσ hx (phiPhase ω)
    (phiPhase_mellin_convergent ω (σ : ℂ) (by simp; linarith))
    (phiPhase_mellin_vertical_integrable σ ω (by linarith))
    (phiPhase_continuous ω).continuousOn

end Helfgott
end

open MeasureTheory Set

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.phi u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((Helfgott.phi ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.phi u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := Helfgott.phi_additive_phase_prime_LFunction_mellin q χ σ x ω hσ hx

#print axioms solution
