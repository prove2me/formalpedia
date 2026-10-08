-- Prove2me | solution 1 for Helfgott.etaPlus_additive_phase_prime_LFunction_mellin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T10:20:33.029768+00:00
-- url     : https://prove2.me/submissions/21970133-ef77-44ce-a46a-1e503afa3549

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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
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
open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logMajorKernel (u : ℝ) : ℝ := majorKernel (Real.exp u)

private noncomputable def logKernelBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^3*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelDBody (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*Real.exp (Real.exp u-1/2)

private noncomputable def logKernelD2Body (u : ℝ) : ℝ :=
  (Real.exp u)^2*(2-Real.exp u)*
    (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
      Real.exp (Real.exp u-1/2)

noncomputable def logMajorKernelD (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelDBody u

noncomputable def logMajorKernelD2 (u : ℝ) : ℝ :=
  (Iic (Real.log 2)).indicator logKernelD2Body u

private lemma logKernelBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelBody (logKernelDBody u) u := by
  have h := Real.hasDerivAt_exp u
  convert! ((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 3)).mul
    ((h.sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [logKernelBody,logKernelDBody] <;> ring

private lemma logKernelDBody_hasDerivAt (u : ℝ) :
    HasDerivAt logKernelDBody (logKernelD2Body u) u := by
  have h := Real.hasDerivAt_exp u
  convert! (((((h.pow 2).mul (((hasDerivAt_const u (2 : ℝ)).sub h).pow 2)).mul
    (h.add_const 4)).mul ((hasDerivAt_const u (1 : ℝ)).sub h)).mul
      ((h.sub_const (1/2 : ℝ)).exp)) using 1 <;>
    dsimp [logKernelDBody,logKernelD2Body] <;> ring

private lemma indicator_Iic_hasDerivAt (f df : ℝ → ℝ) (c : ℝ)
    (hd : ∀ u, HasDerivAt f (df u) u) (hfc : f c = 0) (hdfc : df c = 0) (u : ℝ) :
    HasDerivAt ((Iic c).indicator f) ((Iic c).indicator df u) u := by
  by_cases hu : u ≤ c
  · rw [Set.indicator_of_mem (show u ∈ Iic c from hu)]
    by_cases heq : u = c
    · subst u
      rw [hdfc]
      have hin : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c) c := by
        have h := (hd c).hasDerivWithinAt (s := Iic c)
        rw [hdfc] at h
        apply h.congr
        · intro t ht; simp [Set.indicator_of_mem ht]
        · simp [hfc]
      have hout : HasDerivWithinAt ((Iic c).indicator f) 0 (Iic c)ᶜ c := by
        apply (hasDerivAt_const c (0 : ℝ)).hasDerivWithinAt.congr
        · intro t ht; simp [Set.indicator_of_notMem ht]
        · simp [hfc]
      simpa only [union_compl_self,hasDerivWithinAt_univ] using hin.union hout
    · have hlt : u < c := lt_of_le_of_ne hu heq
      apply (hd u).congr_of_eventuallyEq
      filter_upwards [Iic_mem_nhds hlt] with t ht
      simp [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem (show u ∉ Iic c from hu)]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isClosed_Iic.isOpen_compl.mem_nhds hu] with t ht
    simp [Set.indicator_of_notMem ht]

lemma logMajorKernel_eq_indicator :
    logMajorKernel = (Iic (Real.log 2)).indicator logKernelBody := by
  funext u
  have he : Real.exp u ≤ 2 ↔ u ≤ Real.log 2 := by
    have htwo : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
    constructor
    · intro h
      apply Real.exp_le_exp.mp
      rw [htwo]
      exact h
    · intro h
      simpa only [htwo] using Real.exp_le_exp.mpr h
  by_cases hu : u ≤ Real.log 2
  · have ht : Real.exp u ∈ Icc (0 : ℝ) 2 := ⟨(Real.exp_pos _).le,he.mpr hu⟩
    simp [logMajorKernel,majorKernel,Set.indicator_of_mem ht,
      Set.indicator_of_mem (show u ∈ Iic (Real.log 2) from hu),logKernelBody]
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu (he.mp h.2)
    simp [logMajorKernel,majorKernel,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem (show u ∉ Iic (Real.log 2) from hu)]

theorem logMajorKernel_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernel (logMajorKernelD u) u := by
  rw [logMajorKernel_eq_indicator]
  exact indicator_Iic_hasDerivAt logKernelBody logKernelDBody (Real.log 2)
    logKernelBody_hasDerivAt (by norm_num [logKernelBody,Real.exp_log])
    (by norm_num [logKernelDBody,Real.exp_log]) u

theorem logMajorKernelD_hasDerivAt (u : ℝ) :
    HasDerivAt logMajorKernelD (logMajorKernelD2 u) u := by
  exact indicator_Iic_hasDerivAt logKernelDBody logKernelD2Body (Real.log 2)
    logKernelDBody_hasDerivAt (by norm_num [logKernelDBody,Real.exp_log])
    (by norm_num [logKernelD2Body,Real.exp_log]) u

lemma logMajorKernel_continuous : Continuous logMajorKernel :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernel_hasDerivAt u).continuousAt)

lemma logMajorKernelD_continuous : Continuous logMajorKernelD :=
  continuous_iff_continuousAt.mpr (fun u => (logMajorKernelD_hasDerivAt u).continuousAt)

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
open MeasureTheory Set Filter

namespace Helfgott

noncomputable def logKernelDensity (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)^2*(t+4)*(1-t)*Real.exp (t-1/2)) t

noncomputable def logKernelDensityD2 (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator
    (fun t => t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)) t

private lemma exp_mem_interval (u : ℝ) :
    Real.exp u ∈ Icc (0 : ℝ) 2 ↔ u ∈ Iic (Real.log 2) := by
  have ht : Real.exp (Real.log 2) = (2 : ℝ) := Real.exp_log (by norm_num)
  constructor
  · intro h
    apply Real.exp_le_exp.mp
    simpa only [ht] using h.2
  · intro h
    exact ⟨(Real.exp_pos _).le,by simpa only [ht] using Real.exp_le_exp.mpr h⟩

lemma logMajorKernel_density (u : ℝ) :
    logMajorKernel u = Real.exp u*logKernelDensity (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_mem ht]
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernel,majorKernel,logKernelDensity,Set.indicator_of_notMem ht]

lemma logMajorKernelD_density (u : ℝ) :
    logMajorKernelD u = Real.exp u*logKernelDensityD (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD,logKernelDensityD,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)^2*(Real.exp u+4)*(1-Real.exp u)*
      Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD,logKernelDensityD,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

lemma logMajorKernelD2_density (u : ℝ) :
    logMajorKernelD2 u = Real.exp u*logKernelDensityD2 (Real.exp u) := by
  by_cases hu : u ∈ Iic (Real.log 2)
  · have ht := (exp_mem_interval u).mpr hu
    simp only [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_mem hu,
      Set.indicator_of_mem ht]
    change (Real.exp u)^2*(2-Real.exp u)*
      (16-26*Real.exp u-3*(Real.exp u)^2+7*(Real.exp u)^3+(Real.exp u)^4)*
        Real.exp (Real.exp u-1/2) = _
    ring
  · have ht : Real.exp u ∉ Icc (0 : ℝ) 2 := fun h => hu ((exp_mem_interval u).mp h)
    simp [logMajorKernelD2,logKernelDensityD2,Set.indicator_of_notMem ht,
      Set.indicator_of_notMem hu]

private lemma integrable_interval_density (f : ℝ → ℝ) (hf : Continuous f)
    (h0 : f 0 = 0) (h2 : f 2 = 0) :
    Integrable ((Icc (0 : ℝ) 2).indicator f) := by
  have hc : Continuous ((Icc (0 : ℝ) 2).indicator f) := by
    apply continuous_indicator
    · intro t ht
      have hb := frontier_subset_closure ht
      rw [isClosed_Icc.closure_eq] at hb
      have hn : t ∉ interior (Icc (0 : ℝ) 2) := ht.2
      rw [interior_Icc] at hn
      have he : t=0 ∨ t=2 := by
        by_contra hh
        apply hn
        have h0 : t ≠ 0 := by tauto
        have h2 : t ≠ 2 := by tauto
        exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0),lt_of_le_of_ne hb.2 h2⟩
      rcases he with rfl | rfl <;> assumption
    · exact hf.continuousOn
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  exact Set.indicator_of_notMem ht f

lemma logKernelDensity_integrable : Integrable logKernelDensity := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD_integrable : Integrable logKernelDensityD := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logKernelDensityD2_integrable : Integrable logKernelDensityD2 := by
  exact integrable_interval_density _ (by fun_prop) (by norm_num) (by norm_num)

lemma logMajorKernel_integrable : Integrable logMajorKernel := by
  have h := (integrable_comp_exp_univ logKernelDensity).mpr
    logKernelDensity_integrable.integrableOn
  simpa only [← logMajorKernel_density] using h

lemma logMajorKernelD_integrable : Integrable logMajorKernelD := by
  have h := (integrable_comp_exp_univ logKernelDensityD).mpr
    logKernelDensityD_integrable.integrableOn
  simpa only [← logMajorKernelD_density] using h

lemma logMajorKernelD2_integrable : Integrable logMajorKernelD2 := by
  have h := (integrable_comp_exp_univ logKernelDensityD2).mpr
    logKernelDensityD2_integrable.integrableOn
  simpa only [← logMajorKernelD2_density] using h

lemma logMajorKernelD2_abs_integral :
    (∫ u : ℝ, |logMajorKernelD2 u|) = ∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t| := by
  simpa only [logMajorKernelD2_density,abs_mul,abs_of_pos (Real.exp_pos _)]
    using integral_comp_exp_univ (fun t => |logKernelDensityD2 t|)

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

private noncomputable def variationP (t : ℝ) := t^2*(2-t)^2
private noncomputable def variationPD (t : ℝ) := 4*t*(2-t)*(1-t)
private noncomputable def variationA (t : ℝ) := variationP t*(t+4)*Real.exp (t-1/2)
private noncomputable def variationAD (t : ℝ) :=
  (variationPD t*(t+4)+variationP t*(t+5))*Real.exp (t-1/2)
private noncomputable def variationB (t : ℝ) := (t+4)*(t-1)*Real.exp (t-1/2)
private noncomputable def variationBD (t : ℝ) := (t^2+5*t-1)*Real.exp (t-1/2)
private noncomputable def secondDensityBody (t : ℝ) :=
  t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)*Real.exp (t-1/2)

private lemma variationP_hasDerivAt (t : ℝ) :
    HasDerivAt variationP (variationPD t) t := by
  convert! ((hasDerivAt_id t).pow 2).mul
    (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).pow 2) using 1 <;>
    dsimp [variationP,variationPD] <;> ring

private lemma variationA_hasDerivAt (t : ℝ) :
    HasDerivAt variationA (variationAD t) t := by
  convert! ((variationP_hasDerivAt t).mul ((hasDerivAt_id t).add_const 4)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationA,variationAD] <;> ring

private lemma variationB_hasDerivAt (t : ℝ) :
    HasDerivAt variationB (variationBD t) t := by
  convert! (((hasDerivAt_id t).add_const 4).mul ((hasDerivAt_id t).sub_const 1)).mul
    (((hasDerivAt_id t).sub_const (1/2 : ℝ)).exp) using 1 <;>
    dsimp [variationB,variationBD] <;> ring

private lemma variationP_nonneg (t : ℝ) : 0 ≤ variationP t := by
  dsimp [variationP]; positivity

private lemma variationP_le_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : variationP t ≤ 1 := by
  have h0 : 0 ≤ t*(2-t) := mul_nonneg ht.1 (by linarith [ht.2])
  have h1 : t*(2-t) ≤ 1 := by nlinarith [sq_nonneg (t-1)]
  have h2 := mul_nonneg h0 (sub_nonneg.mpr h1)
  dsimp [variationP]
  nlinarith

private lemma first_interval_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |secondDensityBody t| ≤ variationAD t+5*Real.exp (1/2) := by
  have hp : 0 ≤ variationP t := variationP_nonneg t
  have hpd : 0 ≤ variationPD t := by
    dsimp [variationPD]
    have ht0 : 0 ≤ t := ht.1
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ 1-t := by linarith [ht.2]
    positivity
  have had : 0 ≤ variationAD t := by
    dsimp [variationAD]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h5 : 0 ≤ t+5 := by linarith [ht.1]
    positivity
  have ha : 0 ≤ variationA t := by
    dsimp [variationA]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    positivity
  have ha_le : variationA t ≤ 5*Real.exp (1/2) := by
    have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨ht.1,by linarith [ht.2]⟩)
    have he : Real.exp (t-1/2) ≤ Real.exp (1/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    dsimp [variationA]
    calc
      _ ≤ 1*5*Real.exp (1/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = variationAD t*(1-t)-variationA t := by
    dsimp [secondDensityBody,variationAD,variationA,variationPD,variationP]
    ring
  rw [heq]
  calc
    _ ≤ |variationAD t*(1-t)|+|variationA t| := abs_sub _ _
    _ = variationAD t*(1-t)+variationA t := by
      rw [abs_of_nonneg (mul_nonneg had (by linarith [ht.2])),abs_of_nonneg ha]
    _ ≤ variationAD t+5*Real.exp (1/2) := by
      have h := mul_nonneg had ht.1
      nlinarith

private lemma second_interval_bound {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    |secondDensityBody t| ≤ (-variationPD t)*(6*Real.exp (3/2))+variationBD t := by
  have hp := variationP_nonneg t
  have hp_le := variationP_le_one (show t ∈ Icc (0 : ℝ) 2 from ⟨by linarith [ht.1],ht.2⟩)
  have hpd : 0 ≤ -variationPD t := by
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have h2 : 0 ≤ 2-t := by linarith [ht.2]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht0) h2) h1
    dsimp [variationPD]; nlinarith
  have hb : 0 ≤ variationB t := by
    dsimp [variationB]
    have h4 : 0 ≤ t+4 := by linarith [ht.1]
    have h1 : 0 ≤ t-1 := by linarith [ht.1]
    positivity
  have hbd : 0 ≤ variationBD t := by
    dsimp [variationBD]
    have hq : 0 ≤ t^2+5*t-1 := by nlinarith [sq_nonneg t,ht.1]
    positivity
  have hb_le : variationB t ≤ 6*Real.exp (3/2) := by
    dsimp [variationB]
    have he : Real.exp (t-1/2) ≤ Real.exp (3/2) := Real.exp_le_exp.mpr (by linarith [ht.2])
    calc
      _ ≤ 6*1*Real.exp (3/2) := by gcongr <;> linarith [ht.1,ht.2]
      _ = _ := by ring
  have heq : secondDensityBody t = (-variationPD t)*variationB t-variationP t*variationBD t := by
    dsimp [secondDensityBody,variationPD,variationB,variationP,variationBD]; ring
  rw [heq]
  calc
    _ ≤ |(-variationPD t)*variationB t|+|variationP t*variationBD t| := abs_sub _ _
    _ = (-variationPD t)*variationB t+variationP t*variationBD t := by
      rw [abs_of_nonneg (mul_nonneg hpd hb),abs_of_nonneg (mul_nonneg hp hbd)]
    _ ≤ (-variationPD t)*(6*Real.exp (3/2))+1*variationBD t := by gcongr
    _ = _ := by ring

private lemma first_interval_integral :
    (∫ t in (0 : ℝ)..1, |secondDensityBody t|) ≤ 10*Real.exp (1/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 0 1 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hd : IntervalIntegrable variationAD volume 0 1 :=
    (by unfold variationAD variationPD variationP; fun_prop : Continuous variationAD).intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => 5*Real.exp (1/2)) volume 0 1 :=
    intervalIntegrable_const
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hf (hd.add hc)
    (fun t ht => first_interval_bound ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationA_hasDerivAt t) hd
  rw [intervalIntegral.integral_add hd hc,hi,intervalIntegral.integral_const] at hm
  norm_num [variationA,variationP,smul_eq_mul] at hm ⊢
  linarith

private lemma second_interval_integral :
    (∫ t in (1 : ℝ)..2, |secondDensityBody t|) ≤ 12*Real.exp (3/2) := by
  have hf : IntervalIntegrable (fun t => |secondDensityBody t|) volume 1 2 :=
    (by dsimp [secondDensityBody]; fun_prop : Continuous (fun t => |secondDensityBody t|)).intervalIntegrable _ _
  have hp : IntervalIntegrable variationPD volume 1 2 :=
    (by unfold variationPD; fun_prop : Continuous variationPD).intervalIntegrable _ _
  have hb : IntervalIntegrable variationBD volume 1 2 :=
    (by unfold variationBD; fun_prop : Continuous variationBD).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (1 : ℝ) ≤ 2) hf
    ((hp.neg.mul_const (6*Real.exp (3/2))).add hb) (fun t ht => second_interval_bound ht)
  have hpi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationP_hasDerivAt t) hp
  have hbi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => variationB_hasDerivAt t) hb
  rw [intervalIntegral.integral_add (hp.neg.mul_const _) hb,
    intervalIntegral.integral_mul_const] at hm
  simp only [Pi.neg_apply] at hm
  rw [intervalIntegral.integral_neg,hpi,hbi] at hm
  norm_num [variationP,variationB] at hm ⊢
  linarith

private lemma density_abs_interval :
    (∫ t in Ioi (0 : ℝ), |logKernelDensityD2 t|) = ∫ t in (0 : ℝ)..2, |secondDensityBody t| := by
  have h : (fun t => |logKernelDensityD2 t|) = (Icc (0 : ℝ) 2).indicator
      (fun t => |secondDensityBody t|) := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 2
    · simp [logKernelDensityD2,secondDensityBody,Set.indicator_of_mem ht]
    · simp [logKernelDensityD2,Set.indicator_of_notMem ht]
  rw [h,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hs : Icc (0 : ℝ) 2 ∩ Ioi 0 = Ioc 0 2 := by ext t; simp; constructor <;> intro h <;> grind
  rw [hs,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]

theorem logMajorKernelD2_abs_integral_le : (∫ u : ℝ, |logMajorKernelD2 u|) ≤ 80 := by
  rw [logMajorKernelD2_abs_integral,density_abs_interval]
  have hc : Continuous (fun t => |secondDensityBody t|) := by dsimp [secondDensityBody]; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 1)
    (hc.intervalIntegrable 1 2)]
  have he1 : Real.exp (1/2 : ℝ) ≤ 33/20 := by
    have hs : (Real.exp (1/2 : ℝ))^2 = Real.exp 1 := by
      rw [sq,← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9,Real.exp_pos (1/2 : ℝ)]
  have he3 : Real.exp (3/2 : ℝ) ≤ 9/2 := by
    rw [show (3/2 : ℝ) = 1+1/2 by norm_num,Real.exp_add]
    calc
      _ ≤ (27183/10000 : ℝ)*(33/20) := by
        gcongr
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ _ := by norm_num
  linarith [first_interval_integral,second_interval_integral]

end Helfgott
end

section
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

lemma integrable_of_quadratic_decay (F : ℝ → ℂ) (hc : Continuous F) (A C : ℝ)
    (hb : ∀ ξ : ℝ, ‖F ξ‖ ≤ A) (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) : Integrable F := by
  apply (integrable_inv_one_add_sq.const_mul (A+C)).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun ξ => by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+ξ^2)).mpr
    nlinarith [hb ξ,hd ξ])

lemma inv_square_integrableOn {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun ξ : ℝ => (ξ^2)⁻¹) (Ioi R) := by
  simpa using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR

lemma inv_square_integral {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, (ξ^2)⁻¹) = R⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR
  norm_num [Real.rpow_neg_one] at h
  exact h

lemma quadratic_decay_right_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Ioi R, ‖F ξ‖) ≤ C/R := by
  calc
    _ ≤ ∫ ξ in Ioi R, C*(ξ^2)⁻¹ := by
      apply setIntegral_mono_on hi.norm.integrableOn ((inv_square_integrableOn hR).const_mul C)
        measurableSet_Ioi
      intro ξ hξ
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (sq_pos_of_pos (hR.trans hξ))).mpr
      nlinarith [hd ξ]
    _ = C/R := by rw [integral_const_mul,inv_square_integral hR,div_eq_mul_inv]

lemma integral_left_tail (F : ℝ → ℝ) (R : ℝ) :
    (∫ ξ in Iio (-R), F ξ) = ∫ ξ in Ioi R, F (-ξ) := by
  have him : (fun ξ : ℝ => -ξ) '' Ioi R = Iio (-R) := by
    ext ξ
    simp only [mem_image,mem_Ioi,mem_Iio]
    constructor
    · rintro ⟨u,hu,rfl⟩; linarith
    · intro h; exact ⟨-ξ,by linarith,by simp⟩
  rw [← him]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi R) measurableSet_Ioi
    (fun ξ _ => (hasDerivAt_id ξ).neg.hasDerivWithinAt)
    (fun ξ _ υ _ h => neg_injective h) F
  simpa using h

lemma quadratic_decay_left_tail (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in Iio (-R), ‖F ξ‖) ≤ C/R := by
  rw [integral_left_tail]
  apply quadratic_decay_right_tail (fun ξ => F (-ξ)) hi.comp_neg C _ hR
  intro ξ
  simpa only [neg_sq] using hd (-ξ)

noncomputable def logKernelComplex (u : ℝ) : ℂ := (logMajorKernel u : ℂ)

lemma logKernelComplex_integrable : Integrable logKernelComplex :=
  Complex.ofRealCLM.integrable_comp logMajorKernel_integrable

lemma logKernelComplex_continuous : Continuous logKernelComplex :=
  Complex.continuous_ofReal.comp logMajorKernel_continuous

lemma logKernelComplex_fourier_decay (ξ : ℝ) :
    ξ^2*‖𝓕 logKernelComplex ξ‖ ≤ 80/(4*Real.pi^2) := by
  have h := fourier_second_derivative_decay logKernelComplex_integrable
    (Complex.ofRealCLM.integrable_comp logMajorKernelD_integrable)
    (Complex.ofRealCLM.integrable_comp logMajorKernelD2_integrable)
    (fun u => (logMajorKernel_hasDerivAt u).ofReal_comp)
    (fun u => (logMajorKernelD_hasDerivAt u).ofReal_comp) ξ
  simp only [Function.comp_def,Complex.ofRealCLM_apply,Complex.norm_real,Real.norm_eq_abs] at h
  have hm := logMajorKernelD2_abs_integral_le
  have he : (2*Real.pi*|ξ|)^2 = (4*Real.pi^2)*ξ^2 := by
    nlinarith [sq_abs ξ]
  rw [he] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4*Real.pi^2)).mpr
  nlinarith

lemma logKernelComplex_fourier_integrable : Integrable (𝓕 logKernelComplex) := by
  have hc : Continuous (𝓕 logKernelComplex) := by
    have he : 𝓕 logKernelComplex = VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ ℝ) logKernelComplex := by
      funext ξ
      rw [Real.fourier_eq]
      rfl
    rw [he]
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2))
      logKernelComplex_integrable
  apply integrable_of_quadratic_decay _ hc (∫ u : ℝ, ‖logKernelComplex u‖) (80/(4*Real.pi^2))
  · intro ξ
    rw [Real.fourier_eq]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) logKernelComplex ξ
  · exact logKernelComplex_fourier_decay

end Helfgott
end

section
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def fourierCutoff (F : ℝ → ℂ) (R u : ℝ) : ℂ :=
  ∫ ξ in Icc (-R) R, Real.fourierChar (inner ℝ ξ u) • F ξ

lemma quadratic_decay_outside (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) :
    (∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖) ≤ 2*C/R := by
  have hs : (Icc (-R) R)ᶜ = Iio (-R) ∪ Ioi R := by
    ext ξ
    simp only [mem_compl_iff,mem_Icc,mem_union,mem_Iio,mem_Ioi]
    constructor
    · intro h
      by_cases hx : ξ < -R
      · exact Or.inl hx
      · exact Or.inr (lt_of_not_ge (fun hr => h ⟨le_of_not_gt hx,hr⟩))
    · rintro (h | h) ⟨hl,hr⟩
      · exact (not_lt_of_ge hl) h
      · exact (not_lt_of_ge hr) h
  have hj : Disjoint (Iio (-R)) (Ioi R) := by
    apply disjoint_left.mpr
    intro ξ hl hr
    simp only [mem_Iio,mem_Ioi] at hl hr
    linarith
  rw [hs,setIntegral_union hj measurableSet_Ioi hi.norm.integrableOn hi.norm.integrableOn]
  rw [show 2*C/R=C/R+C/R by ring]
  exact add_le_add (quadratic_decay_left_tail F hi C hd hR)
    (quadratic_decay_right_tail F hi C hd hR)

lemma fourierCutoff_error (F : ℝ → ℂ) (hi : Integrable F) (C : ℝ)
    (hd : ∀ ξ : ℝ, ξ^2*‖F ξ‖ ≤ C) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖fourierCutoff F R u - 𝓕⁻ F u‖ ≤ 2*C/R := by
  have hint : Integrable (fun ξ => Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    apply hi.norm.mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable
    · exact ae_of_all _ (fun ξ => (Circle.norm_smul _ _).le)
  have h := integral_add_compl (s := Icc (-R) R) measurableSet_Icc hint
  have heq : fourierCutoff F R u - 𝓕⁻ F u =
      -(∫ ξ in (Icc (-R) R)ᶜ, Real.fourierChar (inner ℝ ξ u) • F ξ) := by
    rw [fourierCutoff,Real.fourierInv_eq,← h]
    abel
  rw [heq,norm_neg]
  calc
    _ ≤ ∫ ξ in (Icc (-R) R)ᶜ, ‖Real.fourierChar (inner ℝ ξ u) • F ξ‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ in (Icc (-R) R)ᶜ, ‖F ξ‖ := by simp only [Circle.norm_smul]
    _ ≤ _ := quadratic_decay_outside F hi C hd hR

theorem logKernel_fourierCutoff_error {H : ℝ} (hH : 0 < H) (u : ℝ) :
    ‖fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u-logKernelComplex u‖ ≤
      80/(Real.pi*H) := by
  have h := fourierCutoff_error (𝓕 logKernelComplex) logKernelComplex_fourier_integrable
    (80/(4*Real.pi^2)) logKernelComplex_fourier_decay
    (div_pos hH (by positivity : (0 : ℝ) < 2*Real.pi)) u
  rw [logKernelComplex_integrable.fourierInv_fourier_eq logKernelComplex_fourier_integrable
    logKernelComplex_continuous.continuousAt] at h
  have he : 2*(80/(4*Real.pi^2))/(H/(2*Real.pi)) = 80/(Real.pi*H) := by
    field_simp
    <;> ring
  rwa [he] at h

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def cutoffSpectrum (h : ℝ → ℂ) (R : ℝ) (j : ℕ) : ℝ → ℂ :=
  (Icc (-R) R).indicator (fun ξ : ℝ =>
    (-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j*h ξ)

lemma cutoffSpectrum_integrable (h : ℝ → ℂ) (hh : Continuous h) (R : ℝ) (j : ℕ) :
    Integrable (cutoffSpectrum h R j) := by
  have hc : Continuous (fun ξ : ℝ => (-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j*h ξ) :=
    (by fun_prop : Continuous (fun ξ : ℝ => (-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j)).mul hh
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma cutoffSpectrum_real_smul_integrable (h : ℝ → ℂ) (hh : Continuous h) (R : ℝ) (j : ℕ) :
    Integrable (fun ξ : ℝ => ξ • cutoffSpectrum h R j ξ) := by
  have hc : Continuous (fun ξ : ℝ => ξ •
      ((-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j*h ξ)) :=
    (by fun_prop : Continuous (fun ξ : ℝ => ξ)).smul
      ((by fun_prop : Continuous (fun ξ : ℝ => (-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j)).mul hh)
  have he : (fun ξ : ℝ => ξ • cutoffSpectrum h R j ξ) =
      (Icc (-R) R).indicator (fun ξ : ℝ => ξ •
        ((-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ))^j*h ξ)) := by
    funext ξ
    by_cases hξ : ξ ∈ Icc (-R) R <;> simp [cutoffSpectrum, hξ]
  rw [he]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

lemma cutoffSpectrum_fourier_hasDerivAt (h : ℝ → ℂ) (hh : Continuous h)
    (R : ℝ) (j : ℕ) (u : ℝ) :
    HasDerivAt (𝓕 (cutoffSpectrum h R j)) (𝓕 (cutoffSpectrum h R (j+1)) u) u := by
  have hd := Real.hasDerivAt_fourier (cutoffSpectrum_integrable h hh R j)
    (cutoffSpectrum_real_smul_integrable h hh R j) u
  have he : (fun ξ : ℝ => (-2*(Real.pi : ℂ)*Complex.I*(ξ : ℂ)) •
      cutoffSpectrum h R j ξ) = cutoffSpectrum h R (j+1) := by
    funext ξ
    by_cases hξ : ξ ∈ Icc (-R) R
    · simp only [cutoffSpectrum, indicator_of_mem hξ, smul_eq_mul, pow_succ]
      ring
    · simp [cutoffSpectrum, hξ]
  rw [he] at hd
  exact hd

lemma cutoffSpectrum_fourier_continuous (h : ℝ → ℂ) (hh : Continuous h) (R : ℝ) (j : ℕ) :
    Continuous (𝓕 (cutoffSpectrum h R j)) :=
  (show Differentiable ℝ (𝓕 (cutoffSpectrum h R j)) from
    fun u => (cutoffSpectrum_fourier_hasDerivAt h hh R j u).differentiableAt).continuous

lemma cutoffSpectrum_fourier_norm (h : ℝ → ℂ) (R : ℝ) (j : ℕ) (u : ℝ) :
    ‖𝓕 (cutoffSpectrum h R j) u‖ ≤ ∫ ξ : ℝ, ‖cutoffSpectrum h R j ξ‖ := by
  rw [Real.fourier_eq]
  simpa only [VectorFourier.fourierIntegral, innerₗ_apply_apply] using
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (cutoffSpectrum h R j) u

lemma cutoffSpectrum_fourier_mul_integrable (h : ℝ → ℂ) (hh : Continuous h)
    (R : ℝ) (j : ℕ) (g : ℝ → ℂ) (hg : Integrable g) :
    Integrable (fun u : ℝ => 𝓕 (cutoffSpectrum h R j) u*g u) := by
  exact hg.bdd_mul (cutoffSpectrum_fourier_continuous h hh R j).aestronglyMeasurable
    (ae_of_all _ (fun u => cutoffSpectrum_fourier_norm h R j u))

lemma cutoffSpectrum_zero_fourier (h : ℝ → ℂ) (R u : ℝ) :
    𝓕 (cutoffSpectrum h R 0) u = fourierCutoff h R (-u) := by
  rw [Real.fourier_eq]
  unfold cutoffSpectrum fourierCutoff
  simp only [pow_zero, one_mul, ← indicator_smul,
    integral_indicator measurableSet_Icc, Real.inner_apply]
  congr 1
  ext ξ
  congr 2
  ring

noncomputable def cutoffGaussianLog (h : ℝ → ℂ) (R k ω u : ℝ) : ℂ :=
  𝓕 (cutoffSpectrum h R 0) u*gaussianLogPhase k ω u

noncomputable def cutoffGaussianLogDeriv (h : ℝ → ℂ) (R k ω u : ℝ) : ℂ :=
  𝓕 (cutoffSpectrum h R 1) u*gaussianLogPhase k ω u +
    𝓕 (cutoffSpectrum h R 0) u*gaussianLogPhaseDeriv k ω u

noncomputable def cutoffGaussianLogSecond (h : ℝ → ℂ) (R k ω u : ℝ) : ℂ :=
  𝓕 (cutoffSpectrum h R 2) u*gaussianLogPhase k ω u +
    2*(𝓕 (cutoffSpectrum h R 1) u*gaussianLogPhaseDeriv k ω u) +
      𝓕 (cutoffSpectrum h R 0) u*gaussianLogPhaseSecond k ω u

lemma cutoffGaussianLog_integrable (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω : ℝ) (hk : 0 < k) : Integrable (cutoffGaussianLog h R k ω) :=
  cutoffSpectrum_fourier_mul_integrable h hh R 0 _ (gaussianLogPhase_integrable k ω hk)

lemma cutoffGaussianLogDeriv_integrable (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω : ℝ) (hk : 0 < k) : Integrable (cutoffGaussianLogDeriv h R k ω) :=
  (cutoffSpectrum_fourier_mul_integrable h hh R 1 _ (gaussianLogPhase_integrable k ω hk)).add
    (cutoffSpectrum_fourier_mul_integrable h hh R 0 _ (gaussianLogPhaseDeriv_integrable k ω hk))

lemma cutoffGaussianLogSecond_integrable (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω : ℝ) (hk : 0 < k) : Integrable (cutoffGaussianLogSecond h R k ω) :=
  ((cutoffSpectrum_fourier_mul_integrable h hh R 2 _ (gaussianLogPhase_integrable k ω hk)).add
    ((cutoffSpectrum_fourier_mul_integrable h hh R 1 _
      (gaussianLogPhaseDeriv_integrable k ω hk)).const_mul 2)).add
    (cutoffSpectrum_fourier_mul_integrable h hh R 0 _ (gaussianLogPhaseSecond_integrable k ω hk))

lemma cutoffGaussianLog_hasDerivAt (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω u : ℝ) :
    HasDerivAt (cutoffGaussianLog h R k ω) (cutoffGaussianLogDeriv h R k ω u) u :=
  (cutoffSpectrum_fourier_hasDerivAt h hh R 0 u).mul (gaussianLogPhase_hasDerivAt k ω u)

lemma cutoffGaussianLogDeriv_hasDerivAt (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω u : ℝ) :
    HasDerivAt (cutoffGaussianLogDeriv h R k ω) (cutoffGaussianLogSecond h R k ω u) u := by
  have hd := ((cutoffSpectrum_fourier_hasDerivAt h hh R 1 u).mul
    (gaussianLogPhase_hasDerivAt k ω u)).add
    ((cutoffSpectrum_fourier_hasDerivAt h hh R 0 u).mul
      (gaussianLogPhaseDeriv_hasDerivAt k ω u))
  have he :
      (𝓕 (cutoffSpectrum h R (1+1)) u*gaussianLogPhase k ω u +
        𝓕 (cutoffSpectrum h R 1) u*gaussianLogPhaseDeriv k ω u) +
      (𝓕 (cutoffSpectrum h R (0+1)) u*gaussianLogPhaseDeriv k ω u +
        𝓕 (cutoffSpectrum h R 0) u*gaussianLogPhaseSecond k ω u) =
      cutoffGaussianLogSecond h R k ω u := by
    unfold cutoffGaussianLogSecond
    norm_num
    ring
  change HasDerivAt (cutoffGaussianLogDeriv h R k ω)
      ((𝓕 (cutoffSpectrum h R (1+1)) u*gaussianLogPhase k ω u +
        𝓕 (cutoffSpectrum h R 1) u*gaussianLogPhaseDeriv k ω u) +
      (𝓕 (cutoffSpectrum h R (0+1)) u*gaussianLogPhaseDeriv k ω u +
        𝓕 (cutoffSpectrum h R 0) u*gaussianLogPhaseSecond k ω u)) u at hd
  rw [he] at hd
  exact hd

theorem cutoffGaussianLog_fourier_integrable (h : ℝ → ℂ) (hh : Continuous h)
    (R k ω : ℝ) (hk : 0 < k) : Integrable (𝓕 (cutoffGaussianLog h R k ω)) :=
  fourier_integrable_of_two_integrable_derivatives
    (cutoffGaussianLog_integrable h hh R k ω hk)
    (cutoffGaussianLogDeriv_integrable h hh R k ω hk)
    (cutoffGaussianLogSecond_integrable h hh R k ω hk)
    (cutoffGaussianLog_hasDerivAt h hh R k ω)
    (cutoffGaussianLogDeriv_hasDerivAt h hh R k ω)

end Helfgott
end

section
open MeasureTheory Set

namespace Helfgott

theorem mellin_log_integrable_iff (σ : ℝ) (f : ℝ → ℂ) :
    MellinConvergent f (σ : ℂ) ↔
      Integrable (fun u : ℝ => Real.exp (-σ*u) • f (Real.exp (-u))) := by
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
  have he (u : ℝ) : |(-Real.exp (-u))| •
      ((Real.exp (-u) : ℂ)^((σ : ℂ)-1) • f (Real.exp (-u))) =
      Real.exp (-σ*u) • f (Real.exp (-u)) := by
    rw [abs_neg, abs_of_pos (Real.exp_pos _), ← smul_assoc]
    change ((Real.exp (-u) : ℂ)*(Real.exp (-u) : ℂ)^((σ : ℂ)-1))*f (Real.exp (-u)) =
      (Real.exp (-σ*u) : ℂ)*f (Real.exp (-u))
    congr 1
    calc
      (Real.exp (-u) : ℂ)*(Real.exp (-u) : ℂ)^((σ : ℂ)-1) =
          (Real.exp (-u) : ℂ)^(1+((σ : ℂ)-1)) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
          Complex.cpow_one]
      _ = (Real.exp (-σ*u) : ℂ) := by
        have hs : (1 : ℂ)+((σ : ℂ)-1) = (σ : ℂ) := by ring
        rw [hs, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
          ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp,
          ← Complex.ofReal_mul, ← Complex.ofReal_exp]
        congr 2
        ring
  rw [MellinConvergent, ← him,
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj]
  simp only [IntegrableOn, Function.comp_def, he, Measure.restrict_univ]

end Helfgott
end

section
open MeasureTheory Set
open scoped FourierTransform

set_option backward.isDefEq.respectTransparency false

namespace Helfgott

lemma integral_fourierChar_interval (R v : ℝ) (hR : 0 ≤ R) :
    (∫ ξ in Icc (-R) R, (Real.fourierChar (ξ*v) : ℂ)) =
      ((2*R*Real.sinc (2*Real.pi*R*v) : ℝ) : ℂ) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  by_cases hv : v=0
  · subst v
    simp [intervalIntegral.integral_const,Complex.real_smul]
    <;> ring
  · have hc : 2*Real.pi*v ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hv
    calc
      _ = ∫ ξ in -R..R, Complex.exp (((ξ*(2*Real.pi*v) : ℝ) : ℂ)*Complex.I) := by
        apply intervalIntegral.integral_congr
        intro ξ _
        dsimp only
        rw [Real.fourierChar_apply]
        congr 2
        push_cast
        ring
      _ = (2*Real.pi*v)⁻¹ • ∫ t in -(R*(2*Real.pi*v))..R*(2*Real.pi*v),
          Complex.exp ((t : ℂ)*Complex.I) := by
        have h := intervalIntegral.integral_comp_mul_right
          (fun t : ℝ => Complex.exp ((t : ℂ)*Complex.I)) (a := -R) (b := R) hc
        simpa only [neg_mul] using h
      _ = (2*Real.pi*v)⁻¹ • (2*(R*(2*Real.pi*v))*Real.sinc (R*(2*Real.pi*v)) : ℂ) := by
        rw [integral_exp_mul_I_eq_sinc]
        push_cast
        rfl
      _ = _ := by
        rw [Complex.real_smul]
        have he : R*(2*Real.pi*v)=2*Real.pi*R*v := by ring
        rw [he]
        push_cast
        have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
        have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        field_simp [hvC,hpC]
        <;> ring

lemma fourierCutoff_eq_sinc_convolution (f : ℝ → ℂ) (hi : Integrable f)
    (R u : ℝ) (hR : 0 ≤ R) :
    fourierCutoff (𝓕 f) R u = ∫ v : ℝ,
      ((2*R*Real.sinc (2*Real.pi*R*(u-v)) : ℝ) : ℂ)*f v := by
  let g : ℝ → ℝ → ℂ := fun ξ v => Real.fourierChar (inner ℝ ξ (u-v)) • f v
  have hg : Integrable (Function.uncurry g) ((volume.restrict (Icc (-R) R)).prod volume) := by
    apply (hi.norm.comp_snd (volume.restrict (Icc (-R) R))).mono'
    · exact (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
        hi.aestronglyMeasurable.comp_snd
    · exact ae_of_all _ (fun p => (Circle.norm_smul _ _).le)
  have heq : fourierCutoff (𝓕 f) R u = ∫ ξ in Icc (-R) R, ∫ v : ℝ, g ξ v := by
    unfold fourierCutoff
    simp_rw [Real.fourier_eq,Circle.smul_def,smul_eq_mul,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro ξ _
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only [g]
      rw [Circle.smul_def,smul_eq_mul,← mul_assoc,← Circle.coe_mul,← Real.fourierChar.map_add_eq_mul]
      congr 2
      simp only [Real.inner_apply]
      ring)
  rw [heq,integral_integral_swap hg]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [g]
    simp only [Real.inner_apply,Circle.smul_def,smul_eq_mul]
    rw [integral_mul_const,integral_fourierChar_interval R (u-v) hR])

lemma bandLimitedMajorKernel_log_eq (H u : ℝ) :
    bandLimitedMajorKernel H (Real.exp u) = ∫ v : ℝ,
      logMajorKernel (u-v)*(H/Real.pi*Real.sinc (H*v)) := by
  unfold bandLimitedMajorKernel mellinConv
  rw [← integral_comp_exp_univ (fun w => majorKernel (Real.exp u/w)*bandKernel H w/w)]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    unfold logMajorKernel bandKernel
    dsimp only
    rw [Real.log_exp,Real.exp_sub]
    field_simp)

theorem bandLimitedMajorKernel_fourierCutoff (H u : ℝ) (hH : 0 ≤ H) :
    (bandLimitedMajorKernel H (Real.exp u) : ℂ) =
      fourierCutoff (𝓕 logKernelComplex) (H/(2*Real.pi)) u := by
  rw [fourierCutoff_eq_sinc_convolution _ logKernelComplex_integrable _ _
    (div_nonneg hH (by positivity)),bandLimitedMajorKernel_log_eq]
  rw [← integral_complex_ofReal]
  conv_rhs => rw [← integral_sub_left_eq_self _ volume u]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only [logKernelComplex]
    have he : 2*Real.pi*(H/(2*Real.pi))*(u-(u-v))=H*v := by field_simp; ring
    have hc : 2*(H/(2*Real.pi))=H/Real.pi := by field_simp
    rw [he,hc]
    push_cast
    ring)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped FourierTransform

namespace Helfgott

noncomputable def etaPlusPhase (ω t : ℝ) : ℂ :=
  (etaPlus t : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))

lemma logKernelComplex_fourier_continuous : Continuous (𝓕 logKernelComplex) := by
  have he : 𝓕 logKernelComplex = VectorFourier.fourierIntegral
      Real.fourierChar volume (innerₗ ℝ) logKernelComplex := by
    funext ξ
    rw [Real.fourier_eq]
    rfl
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2)) logKernelComplex_integrable

lemma etaPlusPhase_log_kernel (σ ω u : ℝ) :
    Real.exp (-σ*u) • etaPlusPhase ω (Real.exp (-u)) =
      cutoffGaussianLog (𝓕 logKernelComplex) (200/(2*Real.pi)) (σ+1) ω u := by
  have hk : (bandLimitedMajorKernel 200 (Real.exp (-u)) : ℂ) =
      𝓕 (cutoffSpectrum (𝓕 logKernelComplex) (200/(2*Real.pi)) 0) u := by
    rw [cutoffSpectrum_zero_fourier]
    exact bandLimitedMajorKernel_fourierCutoff 200 (-u) (by norm_num)
  unfold etaPlusPhase etaPlus cutoffGaussianLog
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  rw [hk, gaussianLogPhase_shift]
  unfold gaussianLogPhase
  push_cast
  simp only [sub_eq_add_neg, neg_div, Complex.exp_add]
  ring_nf

lemma etaPlusPhase_mellin_convergent (σ ω : ℝ) (hσ : -1 < σ) :
    MellinConvergent (etaPlusPhase ω) (σ : ℂ) := by
  apply (mellin_log_integrable_iff σ (etaPlusPhase ω)).mpr
  simp_rw [etaPlusPhase_log_kernel]
  exact cutoffGaussianLog_integrable (𝓕 logKernelComplex) logKernelComplex_fourier_continuous
    (200/(2*Real.pi)) (σ+1) ω (by linarith)

lemma etaPlusPhase_continuousOn (ω : ℝ) : ContinuousOn (etaPlusPhase ω) (Ioi (0 : ℝ)) := by
  let G := cutoffGaussianLog (𝓕 logKernelComplex) (200/(2*Real.pi)) 1 ω
  have hc : Continuous G :=
    (show Differentiable ℝ G from fun u =>
      (cutoffGaussianLog_hasDerivAt (𝓕 logKernelComplex) logKernelComplex_fourier_continuous
        (200/(2*Real.pi)) 1 ω u).differentiableAt).continuous
  have he (t : ℝ) (ht : 0 < t) : etaPlusPhase ω t = G (-Real.log t) := by
    have h := etaPlusPhase_log_kernel 0 ω (-Real.log t)
    simpa only [neg_neg, neg_zero, zero_mul, Real.exp_zero, one_smul, zero_add,
      Real.exp_log ht] using h
  have hp : ContinuousOn (fun t : ℝ => G (-Real.log t)) (Ioi (0 : ℝ)) := by
    intro t ht
    exact (hc.continuousAt.comp (Real.continuousAt_log ht.ne').neg).continuousWithinAt
  exact hp.congr (fun t ht => he t ht)

theorem etaPlusPhase_mellin_vertical_integrable (σ ω : ℝ) (hσ : -1 < σ) :
    Complex.VerticalIntegrable (mellin (etaPlusPhase ω)) σ := by
  let G := cutoffGaussianLog (𝓕 logKernelComplex) (200/(2*Real.pi)) (σ+1) ω
  have hi := (cutoffGaussianLog_fourier_integrable (𝓕 logKernelComplex)
    logKernelComplex_fourier_continuous (200/(2*Real.pi)) (σ+1) ω (by linarith)).comp_mul_right'
    (by positivity : (1/(2*Real.pi) : ℝ) ≠ 0)
  have he (t : ℝ) : mellin (etaPlusPhase ω) ((σ : ℂ)+(t : ℂ)*Complex.I) =
      𝓕 G (t/(2*Real.pi)) := by
    rw [mellin_eq_fourier]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      Complex.add_im, Complex.mul_im, mul_one, zero_add, etaPlusPhase_log_kernel]
    rfl
  change Integrable (fun t : ℝ => mellin (etaPlusPhase ω) ((σ : ℂ)+(t : ℂ)*Complex.I))
  simp_rw [he]
  simpa only [G, div_eq_mul_inv, one_mul] using hi

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

theorem etaPlus_additive_phase_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (etaPlus u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((etaPlus ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (etaPlus u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := by
  exact twisted_prime_LFunction_mellin q χ σ x hσ hx (etaPlusPhase ω)
    (etaPlusPhase_mellin_convergent σ ω (by linarith))
    (etaPlusPhase_mellin_vertical_integrable σ ω (by linarith))
    (etaPlusPhase_continuousOn ω)

end Helfgott
end

open MeasureTheory Set

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x ω : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
      (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.etaPlus u : ℂ)*
        Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      ((Helfgott.etaPlus ((n : ℝ)/x) : ℂ) *
        Complex.exp (Complex.I*(ω : ℂ)*(((n : ℝ)/x : ℝ) : ℂ))))
      ((1/(2*Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ)*Complex.I
        (x : ℂ)^s * mellin (fun u : ℝ => (Helfgott.etaPlus u : ℂ)*
          Complex.exp (Complex.I*(ω : ℂ)*(u : ℂ))) s *
          (-deriv χ.LFunction s / χ.LFunction s)) := Helfgott.etaPlus_additive_phase_prime_LFunction_mellin q χ σ x ω hσ hx

#print axioms solution
