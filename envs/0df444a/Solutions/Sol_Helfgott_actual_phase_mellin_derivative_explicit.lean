-- Prove2me | solution 1 for Helfgott.actual_phase_mellin_derivative_explicit
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T12:10:37.508188+00:00
-- url     : https://prove2.me/submissions/d7492c68-64ec-466a-b61c-5b11745c188a

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.MellinInversion
import Mathlib.Tactic
import Definitions.Def_Helfgott_Smoothings
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
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Set

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace Helfgott

lemma polynomial_gaussian_isBigO_exp (k : ℕ) (r : ℝ) (hr : 0 < r) :
    (fun t : ℝ => t^k*Real.exp (-r*t^2)) =O[atTop] (fun t : ℝ => Real.exp (-t)) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop k (b := 1) (by norm_num)).isBigO
  have hg : (fun t : ℝ => t^k*Real.exp (-r*t^2)) =O[atTop]
      (fun t : ℝ => t^k*Real.exp (-2*t)) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (max 0 (2/r))] with t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hrt : 2 ≤ r*t := by
      have h := (le_max_right 0 (2/r)).trans ht
      simpa only [mul_comm] using (div_le_iff₀ hr).mp h
    have he : Real.exp (-r*t^2) ≤ Real.exp (-2*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hrt ht0]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 k),
      abs_of_pos (Real.exp_pos _), one_mul]
    exact mul_le_mul_of_nonneg_left he (pow_nonneg ht0 k)
  have hm := hp.mul (isBigO_refl (fun t : ℝ => Real.exp (-2*t)) atTop)
  have he (t : ℝ) : Real.exp (1*t)*Real.exp (-2*t) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact hg.trans (hm.congr_right he)

lemma gaussian_envelope_mellin_hasDerivAt (k : ℕ) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (f : ℝ → ℂ) (hfc : ContinuousOn f (Ioi 0))
    (hf : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ C*t^k*Real.exp (-r*t^2))
    (s : ℂ) (hs : -(k : ℝ) < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t : ℝ => Real.log t • f t) s) s := by
  have htop : f =O[atTop] (fun t : ℝ => t^k*Real.exp (-r*t^2)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht0 : 0 < t := ht
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0.le k),
      abs_of_pos (Real.exp_pos _), mul_assoc] using hf t ht
  have hbot : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t^k) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    have he : Real.exp (-r*t^2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg hr.le (sq_nonneg t)]
    have hb := (hf t ht).trans (mul_le_of_le_one_right
      (mul_nonneg hC (pow_nonneg ht0.le k)) he)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0.le k)] using hb
  have hbr : f =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-(-(k : ℝ)))) := by
    simpa only [neg_neg, Real.rpow_natCast] using hbot
  have he : (fun t : ℝ => Real.exp (-t)) =O[atTop]
      (fun t : ℝ => t ^ (-(s.re+1))) := by
    simpa only [neg_mul, one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop (a := 1) (by norm_num) (-(s.re+1))).isBigO
  have ht := (htop.trans (polynomial_gaussian_isBigO_exp k r hr)).trans he
  exact mellin_hasDerivAt_of_isBigO_rpow
    (hfc.locallyIntegrableOn measurableSet_Ioi) ht (by linarith) hbr hs

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
open MeasureTheory Set Filter

namespace Helfgott

private noncomputable def weightedMajorKernel (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

private lemma weightedMajorKernel_nonneg (t : ℝ) : 0 ≤ weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · rw [weightedMajorKernel,indicator_of_mem ht]
    have h : 0 ≤ 2-t := by linarith [ht.2]
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_continuous : Continuous weightedMajorKernel := by
  unfold weightedMajorKernel
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
    rcases he with rfl | rfl <;> norm_num
  · exact (by fun_prop : Continuous (fun t : ℝ => t*(2-t)^3*Real.exp (t-1/2))).continuousOn

private lemma weightedMajorKernel_compact : HasCompactSupport weightedMajorKernel := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_integrable : Integrable weightedMajorKernel :=
  weightedMajorKernel_continuous.integrable_of_hasCompactSupport weightedMajorKernel_compact

private lemma majorKernel_eq_weighted (t : ℝ) : majorKernel t = t*weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · simp only [majorKernel,weightedMajorKernel,indicator_of_mem ht]
    ring
  · simp [majorKernel,weightedMajorKernel,ht]

lemma bandKernel_abs_le (H w : ℝ) : |bandKernel H w| ≤ |H|/Real.pi := by
  unfold bandKernel
  rw [abs_mul,abs_div,abs_of_pos Real.pi_pos]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

private lemma inverse_major_integrand (H t v : ℝ) (hv : 0 < v) :
    majorKernel (t/v⁻¹)*bandKernel H v⁻¹/v =
      t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  rw [div_inv_eq_mul,majorKernel_eq_weighted]
  field_simp

private lemma inverse_major_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) (Ioi (0 : ℝ)) := by
  have hk := weightedMajorKernel_continuous
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  apply (hi.mul_const (|H|/Real.pi)).mono'
  · have hm : Measurable (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) := by
      unfold bandKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
      exact mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _)))

lemma bandLimitedMajorKernel_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => majorKernel (t/w)*bandKernel H w/w) (Ioi (0 : ℝ)) := by
  apply (integrable_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)).mpr
  apply (inverse_major_integrable H t ht).congr_fun _ measurableSet_Ioi
  intro v hv
  exact (inverse_major_integrand H t v hv).symm

lemma bandLimitedMajorKernel_inverse (H t : ℝ) :
    bandLimitedMajorKernel H t =
      ∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  unfold bandLimitedMajorKernel mellinConv
  rw [integral_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact inverse_major_integrand H t v hv

private lemma bandLimitedMajorKernel_abs_le_pos (H t : ℝ) (ht : 0 < t) :
    |bandLimitedMajorKernel H t| ≤ (|H|/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v) := by
  rw [bandLimitedMajorKernel_inverse]
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  have hn : |∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹| ≤
      ∫ v in Ioi (0 : ℝ), (|H|/Real.pi)*(t*weightedMajorKernel (t*v)) := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (inverse_major_integrable H t ht).norm (hi.const_mul (|H|/Real.pi))
    intro v
    dsimp only
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
    convert! mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
      (mul_nonneg ht.le (weightedMajorKernel_nonneg _)) using 1 <;> ring
  refine hn.trans_eq ?_
  rw [integral_const_mul,integral_const_mul,integral_comp_mul_left_Ioi weightedMajorKernel 0 ht]
  simp only [mul_zero,smul_eq_mul]
  field_simp

lemma majorKernel_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : majorKernel t = 0 := by
  by_cases hz : t = 0
  · subst t; simp [majorKernel]
  · have hn : t ∉ Icc (0 : ℝ) 2 := by intro h; exact hz (le_antisymm ht h.1)
    simp [majorKernel,hn]

lemma bandLimitedMajorKernel_zero_of_nonpos (H t : ℝ) (ht : t ≤ 0) :
    bandLimitedMajorKernel H t = 0 := by
  unfold bandLimitedMajorKernel mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [majorKernel_zero_of_nonpos (t/w) (div_nonpos_of_nonpos_of_nonneg ht hw.le)]
  simp

theorem etaPlus_gaussian_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |etaPlus t| ≤ C*|t| *Real.exp (-(t^2)/2) := by
  let C : ℝ := ((200 : ℝ)/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (integral_nonneg weightedMajorKernel_nonneg)
  refine ⟨C,hC,?_⟩
  intro t
  have hb : |bandLimitedMajorKernel 200 t| ≤ C := by
    by_cases ht : 0 < t
    · simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 200)] using
        bandLimitedMajorKernel_abs_le_pos 200 t ht
    · rw [bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht),abs_zero]
      exact hC
  unfold etaPlus
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (abs_nonneg t)) (Real.exp_pos _).le

end Helfgott
end

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_scaled_zero (T w : ℝ) (hT : 0 < T) (hw : w ∉ Icc T (4*T)) :
    etaTwo (T/w) = 0 := by
  by_cases hwp : 0 < w
  · apply etaTwo_eq_zero_of_not_mem
    intro h
    apply hw
    constructor
    · simpa using (div_le_iff₀ hwp).mp h.2
    · have hh := (le_div_iff₀ hwp).mp h.1
      nlinarith
  · have hh : T/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_gt hwp)
    simp [etaTwo, not_lt_of_ge hh]

lemma etaTwo_scaled_weight_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => etaTwo (T/w)/w) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hT] with x hx
    change x < T at hx
    rw [etaTwo_scaled_zero T x hT (by intro hm; linarith [hm.1]), zero_div]
  · have hc : ContinuousAt (fun x : ℝ => T/x) w := by fun_prop
    exact (etaTwo_continuous.continuousAt.comp hc).div continuousAt_id hw

lemma etaTwo_scaled_weight_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)/w) := by
  apply (etaTwo_scaled_weight_continuous T hT).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
  intro w hw
  rw [etaTwo_scaled_zero T w hT hw,zero_div]

lemma etaTwo_scaled_lower (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (2*T)) :
    etaTwo (T/w) = 4 * (Real.log w - Real.log T) := by
  have hwp : 0 < w := lt_of_lt_of_le hT hw.1
  have hm : T/w ∈ Icc (1/2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; simpa using hw.1
  rw [etaTwo_eq_upper _ hm, Real.log_div hT.ne' hwp.ne']
  ring

lemma etaTwo_scaled_upper (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc (2*T) (4*T)) :
    etaTwo (T/w) = 4 * (Real.log (4*T) - Real.log w) := by
  have hwp : 0 < w := by linarith [hw.1]
  have hm : T/w ∈ Icc (1/4 : ℝ) (1/2) := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; linarith [hw.1]
  rw [etaTwo_eq_lower _ hm]
  rw [show 4*(T/w) = (4*T)/w by ring,
    Real.log_div (by positivity : 4*T ≠ 0) hwp.ne']

theorem etaTwo_scaled_log_mass (T : ℝ) (hT : 0 < T) :
    (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) = 4 * (Real.log 2)^2 := by
  have hf := etaTwo_scaled_weight_continuous T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun w => etaTwo (T/w)/w) volume a b :=
    hf.intervalIntegrable _ _
  have hrestrict : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) =
      ∫ w in T..4*T, etaTwo (T/w)/w := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc T (4*T) ⊆ Ioi (0 : ℝ) by intro w hw; exact lt_of_lt_of_le hT hw.1)
      (show ∀ w ∈ Ioi (0 : ℝ) \ Icc T (4*T), etaTwo (T/w)/w = 0 by
        intro w hw; rw [etaTwo_scaled_zero T w hT hw.2,zero_div])]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals (hi T (2*T)) (hi (2*T) (4*T))]
  have hlo : (∫ w in T..2*T, etaTwo (T/w)/w) =
      2*(Real.log (2*T)-Real.log T)^2 := by
    have heq : (∫ w in T..2*T, etaTwo (T/w)/w) =
        ∫ w in T..2*T, 4*(Real.log w-Real.log T)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      dsimp only
      rw [etaTwo_scaled_lower T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log w-Real.log T)/w)
        volume T (2*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc T (2*T)) :
        HasDerivAt (fun w : ℝ => 2*(Real.log w-Real.log T)^2)
          (4*(Real.log w-Real.log T)/w) w := by
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').sub_const (Real.log T)).pow 2).const_mul 2 using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hhi : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
      2*(Real.log (4*T)-Real.log (2*T))^2 := by
    have heq : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
        ∫ w in 2*T..4*T, 4*(Real.log (4*T)-Real.log w)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      dsimp only
      rw [etaTwo_scaled_upper T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log (4*T)-Real.log w)/w)
        volume (2*T) (4*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc (2*T) (4*T)) :
        HasDerivAt (fun w : ℝ => -2*(Real.log (4*T)-Real.log w)^2)
          (4*(Real.log (4*T)-Real.log w)/w) w := by
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').const_sub (Real.log (4*T))).pow 2).const_mul (-2) using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  rw [hlo,hhi,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

lemma phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2/2)
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [he] at h
  unfold phi
  have heq : -(t^2/2) = -(t^2)/2 := by ring
  rw [heq] at h
  calc
    t^2*Real.exp (-(t^2)/2) = 2*((t^2/2)*Real.exp (-(t^2)/2)) := by ring
    _ ≤ 2*(Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2/Real.exp 1 := by ring

lemma mellin_etaTwo_phi_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)*phi w/w) := by
  have hphi : Continuous phi := by unfold phi; fun_prop
  have hc : Continuous (fun w : ℝ => (etaTwo (T/w)/w)*phi w) :=
    (etaTwo_scaled_weight_continuous T hT).mul hphi
  have hs : HasCompactSupport (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
    intro w hw
    rw [etaTwo_scaled_zero T w hT hw,zero_div,zero_mul]
  have hh : Integrable (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := hc.integrable_of_hasCompactSupport hs
  have heq : (fun w : ℝ => etaTwo (T/w)*phi w/w) = (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    funext w; ring
  rw [heq]
  exact hh

lemma mellin_etaTwo_phi_nonneg (T : ℝ) : 0 ≤ mellinConv etaTwo phi T := by
  unfold mellinConv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) (le_of_lt hw)

lemma mellin_etaTwo_phi_le (T : ℝ) :
    mellinConv etaTwo phi T ≤ 8*(Real.log 2)^2/Real.exp 1 := by
  by_cases hT : 0 < T
  · have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul (2/Real.exp 1)).restrict
      (s := Ioi (0 : ℝ))
    have hbound : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), (2/Real.exp 1)*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have he := mul_le_mul_of_nonneg_left (phi_le w) (etaTwo_nonneg (T/w))
      have hh := div_le_div_of_nonneg_right he (le_of_lt hw)
      convert! hh using 1 <;> ring
    unfold mellinConv
    refine hbound.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    ring
  · have hz : mellinConv etaTwo phi T = 0 := by
      unfold mellinConv
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) (le_of_lt hw)
      simp [etaTwo,not_lt_of_ge hh]
    rw [hz]
    positivity

lemma mellin_etaTwo_phi_le_rational (T : ℝ) :
    mellinConv etaTwo phi T ≤ (707/500 : ℝ) := by
  apply (mellin_etaTwo_phi_le T).trans
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : (Real.log 2)^2 ≤ (0.6931471808 : ℝ)^2 :=
    pow_le_pow_left₀ hlog Real.log_two_lt_d9.le 2
  nlinarith only [hs, Real.exp_one_gt_d9]

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707/500 : ℝ) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg (49*t))]
  exact mellin_etaTwo_phi_le_rational (49*t)

end Helfgott
end

section
open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_etaTwo_phi_zero (T : ℝ) (hT : T ≤ 0) : mellinConv etaTwo phi T = 0 := by
  unfold mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg hT (le_of_lt hw)
  simp [etaTwo,not_lt_of_ge hh]

lemma phi_le_on_scaled_support (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (4*T)) :
    phi w ≤ (4*T)^2*Real.exp (-(T^2)/2) := by
  have hwp : 0 ≤ w := le_trans hT.le hw.1
  have hslo : T^2 ≤ w^2 := pow_le_pow_left₀ hT.le hw.1 2
  have hshi : w^2 ≤ (4*T)^2 := pow_le_pow_left₀ hwp hw.2 2
  have he : Real.exp (-(w^2)/2) ≤ Real.exp (-(T^2)/2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold phi
  exact mul_le_mul hshi he (Real.exp_pos _).le (sq_nonneg _)

theorem mellin_etaTwo_phi_gaussian_decay (T : ℝ) :
    mellinConv etaTwo phi T ≤ 64*(Real.log 2)^2*T^2*Real.exp (-(T^2)/2) := by
  by_cases hT : 0 < T
  · let C : ℝ := (4*T)^2*Real.exp (-(T^2)/2)
    have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul C).restrict (s := Ioi (0 : ℝ))
    have hb : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), C*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      by_cases hm : w ∈ Icc T (4*T)
      · have he := mul_le_mul_of_nonneg_left (phi_le_on_scaled_support T w hT hm)
          (etaTwo_nonneg (T/w))
        have hh := div_le_div_of_nonneg_right he hw.le
        convert! hh using 1 <;> dsimp [C] <;> ring
      · rw [etaTwo_scaled_zero T w hT hm]
        simp
    unfold mellinConv
    refine hb.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    dsimp [C]
    ring
  · rw [mellin_etaTwo_phi_zero T (le_of_not_gt hT)]
    positivity

theorem etaStar_abs_le_gaussian (t : ℝ) :
    |etaStar t| ≤ 64*(Real.log 2)^2*(49*t)^2*Real.exp (-((49*t)^2)/2) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg _)]
  exact mellin_etaTwo_phi_gaussian_decay (49*t)

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology

namespace Helfgott

lemma etaPlusPhase_mellin_hasDerivAt (ω : ℝ) (s : ℂ) (hs : -1 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • etaPlusPhase ω t) s ∧
      HasDerivAt (mellin (etaPlusPhase ω))
        (mellin (fun t : ℝ => Real.log t • etaPlusPhase ω t) s) s := by
  obtain ⟨C,hC,hb⟩ := etaPlus_gaussian_envelope
  apply gaussian_envelope_mellin_hasDerivAt 1 (1/2) C (by norm_num) hC
    (etaPlusPhase ω) (etaPlusPhase_continuousOn ω) _ s (by simpa using hs)
  intro t ht
  have hn : ‖etaPlusPhase ω t‖ = |etaPlus t| := by
    unfold etaPlusPhase
    rw [norm_mul, additivePhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hn]
  have he : -(t^2)/2 = -(1/2)*t^2 := by ring
  simpa only [abs_of_pos ht, pow_one, he] using hb t

lemma etaStarPhase_mellin_hasDerivAt (ω : ℝ) (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • etaStarPhase ω t) s ∧
      HasDerivAt (mellin (etaStarPhase ω))
        (mellin (fun t : ℝ => Real.log t • etaStarPhase ω t) s) s := by
  let C : ℝ := 64*(Real.log 2)^2*49^2
  apply gaussian_envelope_mellin_hasDerivAt 2 (49^2/2) C (by norm_num) (by dsimp [C]; positivity)
    (etaStarPhase ω) (etaStarPhase_continuous ω).continuousOn _ s (by simpa using hs)
  intro t ht
  rw [etaStarPhase_norm, Complex.norm_real, Real.norm_eq_abs]
  refine (etaStar_abs_le_gaussian t).trans_eq ?_
  dsimp [C]
  congr 1
  · ring
  · congr 1; ring

theorem actual_phase_mellin_hasDerivAt (η : ℝ → ℝ) (hη : η=etaPlus ∨ η=etaStar)
    (ω : ℝ) (s : ℂ) (hs : -1 < s.re) :
    let f : ℝ → ℂ := fun t => (η t : ℂ)*Complex.exp (Complex.I*(ω : ℂ)*(t : ℂ))
    MellinConvergent (fun t : ℝ => Real.log t • f t) s ∧
      HasDerivAt (mellin f) (mellin (fun t : ℝ => Real.log t • f t) s) s := by
  rcases hη with rfl | rfl
  · exact etaPlusPhase_mellin_hasDerivAt ω s hs
  · exact etaStarPhase_mellin_hasDerivAt ω s (by linarith)

end Helfgott
end

open MeasureTheory Set

theorem solution (η : ℝ → ℝ) (hη : η = Helfgott.etaPlus ∨ η = Helfgott.etaStar)
    (ω : ℝ) (s : ℂ) (hs : -1 < Complex.re s) :
    MellinConvergent (fun t : ℝ => Real.log t •
      ((η t : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)))) s ∧
    HasDerivAt (mellin (fun t : ℝ =>
      (η t : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))))
      (mellin (fun t : ℝ => Real.log t •
        ((η t : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)))) s) s := Helfgott.actual_phase_mellin_hasDerivAt η hη ω s hs

#print axioms solution
