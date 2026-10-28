-- Prove2me | solution 1 for OAI.PlanarFalconer.full_circle_stationary_expansion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:08:37.154423+00:00
-- url     : https://prove2.me/submissions/37637d92-b961-4767-bc55-26e6faf75e15

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_QuadraticGaussianPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

 theorem fourier_quadraticGaussian {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp (-a*(x:ℂ)^2)) ξ = quadraticFourierKernel a ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : ((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I =
      Complex.I * ((-2*Real.pi*ξ:ℝ):ℂ) * (x:ℂ) := by push_cast; ring
  simp_rw [smul_eq_mul,he]
  rw [fourierIntegral_gaussian ha]
  unfold quadraticFourierKernel
  congr 3
  push_cast
  ring

 theorem quadraticGaussian_pairing {a : ℂ} (ha : 0 < a.re) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-a*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, quadraticFourierKernel a ξ * φ ξ := by
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner (integrable_cexp_neg_mul_sq ha) φ.integrable
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; rfl
  rw [hflip] at hh
  have he : (∫ x : ℝ, Complex.exp (-a*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, 𝓕 (fun x : ℝ => Complex.exp (-a*(x:ℂ)^2)) ξ * φ ξ := by
    simpa only [smul_eq_mul] using! hh.symm
  rw [he]
  simp only [fourier_quadraticGaussian ha]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_QuadraticKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem quadratic_exponential_norm_le_one {a : ℂ} (ha : 0 ≤ a.re) (s : ℝ) :
    ‖Complex.exp (-((s:ℂ)^2)/(4*a))‖ ≤ 1 := by
  have he : -((s:ℂ)^2)/(4*a) = ((-s^2/4:ℝ):ℂ)*a⁻¹ := by
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,Complex.norm_exp,Complex.re_ofReal_mul]
  apply Real.exp_le_one_iff.mpr
  have hi : 0 ≤ a⁻¹.re := by rw [Complex.inv_re]; exact div_nonneg ha (Complex.normSq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (by norm_num)) hi

 theorem quadraticFourierKernel_norm_bound {a : ℂ} (ha : 0 ≤ a.re)
    {b : ℝ} (hb : 0 < b) (hn : b ≤ ‖a‖) (ξ : ℝ) :
    ‖quadraticFourierKernel a ξ‖ ≤ (Real.pi/b)^(1/2:ℝ) := by
  unfold quadraticFourierKernel
  rw [norm_mul]
  have hpow : ‖((Real.pi:ℂ)/a)^(1/2:ℂ)‖ = (Real.pi/‖a‖)^(1/2:ℝ) := by
    convert Complex.norm_cpow_real ((Real.pi:ℂ)/a) (1/2:ℝ) using 1 <;>
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hpow]
  calc
    _ ≤ (Real.pi/‖a‖)^(1/2:ℝ)*1 := mul_le_mul_of_nonneg_left
      (quadratic_exponential_norm_le_one ha _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left Real.pi_pos.le hb hn) (by norm_num)

 theorem quadraticFourierKernel_damped_bound {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 ≤ ε) (ξ : ℝ) :
    ‖quadraticFourierKernel ((ε:ℂ)+(b:ℂ)*Complex.I) ξ‖ ≤ (Real.pi/b)^(1/2:ℝ) := by
  apply quadraticFourierKernel_norm_bound (by simpa using hε) hb
  have hh := Complex.abs_im_le_norm ((ε:ℂ)+(b:ℂ)*Complex.I)
  simpa [abs_of_pos hb] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_QuadraticDampingLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

 theorem quadraticFourierKernel_continuous_damping {b : ℝ} (hb : 0 < b) (ξ : ℝ) :
    ContinuousAt (fun ε : ℝ => quadraticFourierKernel ((ε:ℂ)+(b:ℂ)*Complex.I) ξ) 0 := by
  have hn : (b:ℂ)*Complex.I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne') Complex.I_ne_zero
  unfold quadraticFourierKernel
  apply ContinuousAt.mul
  · have ht : ContinuousAt (fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) 0 :=
      continuousAt_const.div (by fun_prop) (by simpa using hn)
    have hp : ContinuousAt (fun z : ℂ => z^(1/2:ℂ))
        ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)) :=
      Complex.continuousAt_cpow_const_of_re_pos
        (Or.inl (show 0 ≤ ((Real.pi:ℂ)/((0:ℂ)+(b:ℂ)*Complex.I)).re by simp [Complex.div_re]))
        (show 0 < (1/2:ℂ).re by norm_num)
    exact hp.comp (f := fun ε : ℝ => (Real.pi:ℂ)/((ε:ℂ)+(b:ℂ)*Complex.I)) (x := 0) ht
  · apply Complex.continuous_exp.continuousAt.comp
    exact continuousAt_const.div (by fun_prop) (by simpa using mul_ne_zero (by norm_num : (4:ℂ) ≠ 0) hn)

 theorem quadraticFourierKernel_integral_limit {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    Tendsto (fun c : ℝ => ∫ ξ : ℝ,
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) atTop
      (𝓝 (∫ ξ : ℝ, quadraticFourierKernel ((b:ℂ)*Complex.I) ξ * φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun ξ => (Real.pi/b)^(1/2:ℝ)*‖φ ξ‖) _ _ (φ.integrable.norm.const_mul _) _
  · filter_upwards with c
    exact (show Continuous (fun ξ : ℝ =>
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) by
        unfold quadraticFourierKernel; fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (quadraticFourierKernel_damped_bound hb (inv_nonneg.mpr hc) ξ) (norm_nonneg _)
  · filter_upwards with ξ
    have hh := (quadraticFourierKernel_continuous_damping hb ξ).tendsto.comp tendsto_inv_atTop_zero
    simpa using hh.mul_const (φ ξ)

 theorem quadraticGaussian_integral_limit {b : ℝ} (φ : 𝓢(ℝ,ℂ)) :
    Tendsto (fun c : ℝ => ∫ x : ℝ,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖𝓕 φ x‖) _ _ (𝓕 φ).integrable.norm _
  · filter_upwards with c
    exact (show Continuous (fun x : ℝ =>
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) by fun_prop).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (0:ℝ)] with c hc
    filter_upwards with x
    rw [norm_mul]
    have hh : ‖Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2)‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.add_re,Complex.add_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,← Complex.ofReal_pow]
      simp only [mul_zero,add_zero,zero_add,sub_zero,mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg x)
    exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    have hh := ((tendsto_inv_atTop_zero.ofReal.add_const ((b:ℂ)*Complex.I)).neg.mul_const ((x:ℂ)^2)).cexp
    simpa using hh.mul_const (𝓕 φ x)

 theorem quadratic_oscillatory_pairing {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) =
      ∫ ξ : ℝ, quadraticFourierKernel ((b:ℂ)*Complex.I) ξ * φ ξ := by
  have he : (fun c : ℝ => ∫ x : ℝ,
      Complex.exp (-(((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)*(x:ℂ)^2) * 𝓕 φ x) =ᶠ[atTop]
      (fun c : ℝ => ∫ ξ : ℝ,
      quadraticFourierKernel (((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I) ξ * φ ξ) := by
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with c hc
    exact quadraticGaussian_pairing (a := ((c⁻¹:ℝ):ℂ)+(b:ℂ)*Complex.I)
      (by simpa using inv_pos.mpr (show 0 < c from hc)) φ
  exact tendsto_nhds_unique (quadraticGaussian_integral_limit φ)
    ((quadraticFourierKernel_integral_limit hb φ).congr' he.symm)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_QuadraticStationaryIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem quadratic_fresnel_coefficient {b : ℝ} (hb : 0 < b) :
    ((Real.pi:ℂ)/((b:ℂ)*Complex.I))^(1/2:ℂ) =
      (((Real.pi/b)^(1/2:ℝ):ℝ):ℂ) * Complex.exp (-(Real.pi:ℂ)/4*Complex.I) := by
  have hr : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hi : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
  have he : (Real.pi:ℂ)/((b:ℂ)*Complex.I) = ((Real.pi/b:ℝ):ℂ)*(-Complex.I) := by
    push_cast
    field_simp
    simp [Complex.I_sq,div_eq_mul_inv]
  rw [he,Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hi),
    Complex.log_ofReal_mul hr hi,Complex.log_neg_I]
  have hex : (((Real.log (Real.pi/b):ℝ):ℂ)+(-((Real.pi:ℂ)/2)*Complex.I))*(1/2:ℂ) =
      ((Real.log (Real.pi/b):ℝ):ℂ)*(1/2:ℂ) + (-(Real.pi:ℂ)/4*Complex.I) := by ring
  rw [hex,Complex.exp_add]
  congr 1
  rw [Real.rpow_def_of_pos hr]
  push_cast
  rfl

 theorem quadratic_imaginary_exponent {b : ℝ} (hb : 0 < b) (s : ℝ) :
    -((s:ℂ)^2)/(4*((b:ℂ)*Complex.I)) = Complex.I*((s:ℂ)^2/(4*(b:ℂ))) := by
  field_simp [Complex.ofReal_ne_zero.mpr hb.ne']
  simp [Complex.I_sq]

 theorem quadratic_stationary_identity {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2) * φ x) =
      ((((Real.pi/b)^(1/2:ℝ):ℝ):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) *
      ∫ ξ : ℝ, Complex.exp (Complex.I*(((2*Real.pi*ξ:ℝ):ℂ)^2/(4*(b:ℂ)))) * 𝓕⁻ φ ξ := by
  have hh := quadratic_oscillatory_pairing hb (𝓕⁻ φ)
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  rw [hh]
  simp only [quadraticFourierKernel,quadratic_fresnel_coefficient hb,quadratic_imaginary_exponent hb]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_OscillatoryTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem imaginaryExponential_contDiff : ContDiff ℝ ∞ imaginaryExponential := by
  unfold imaginaryExponential
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (t:ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

 theorem imaginaryExponential_hasDerivAt (t : ℝ) :
    HasDerivAt imaginaryExponential (Complex.I*imaginaryExponential t) t := by
  unfold imaginaryExponential
  convert (((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).cexp) using 1 <;>
    simp [mul_comm]

 theorem imaginaryExponential_iteratedDeriv (n : ℕ) :
    iteratedDeriv n imaginaryExponential = fun t => Complex.I^n * imaginaryExponential t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    rw [((imaginaryExponential_hasDerivAt t).const_mul (Complex.I^n)).deriv,pow_succ]
    ring

 theorem imaginaryExponential_derivative_norm (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n imaginaryExponential t‖ = 1 := by
  rw [imaginaryExponential_iteratedDeriv]
  simp [imaginaryExponential,Complex.norm_exp,Complex.mul_re]

 theorem imaginaryExponential_taylor_bound (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ‖imaginaryExponential t - imaginaryTaylor n t‖ ≤ t^(n+1)/(n.factorial:ℝ) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [imaginaryTaylor,imaginaryExponential,zero_pow_eq]
  have hd : UniqueDiffOn ℝ (Icc 0 t) := uniqueDiffOn_Icc ht
  have hs (k : ℕ) : ContDiff ℝ k imaginaryExponential :=
    imaginaryExponential_contDiff.of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
  have hh := taylor_mean_remainder_bound ht.le (hs (n+1)).contDiffOn
    (show t ∈ Icc 0 t from ⟨ht.le,le_rfl⟩) (C := 1) (fun y hy => by
      rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs (n+1)).contDiffAt hy,
        imaginaryExponential_derivative_norm])
  have he : taylorWithinEval imaginaryExponential n (Icc 0 t) 0 t = imaginaryTaylor n t := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv hd (hs k).contDiffAt (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl,ht.le⟩),
      imaginaryExponential_iteratedDeriv]
    simp [imaginaryExponential]
  simpa only [he,sub_zero,one_mul] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_QuadraticTaylorRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped FourierTransform SchwartzMap

 theorem schwartz_monomial_integrable (φ : 𝓢(ℝ,ℂ)) (p : ℕ) :
    Integrable (fun x : ℝ => (x:ℂ)^p * φ x) := by
  apply (φ.integrable_pow_mul volume p).mono' (by fun_prop)
  filter_upwards with x
  simp [norm_pow, Complex.norm_real]

 theorem imaginaryTaylor_quadratic_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (β : ℝ) :
    Integrable (fun x => imaginaryTaylor n (β*x^2) * φ x) := by
  have he : (fun x => imaginaryTaylor n (β*x^2)*φ x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ((x:ℂ)^(2*k)*φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,mul_pow,pow_mul]
    ring
  rw [he]
  apply integrable_finsetSum
  intro k _
  exact (schwartz_monomial_integrable φ (2*k)).const_mul _

 theorem imaginaryExponential_quadratic_integrable (φ : 𝓢(ℝ,ℂ)) (β : ℝ) :
    Integrable (fun x => imaginaryExponential (β*x^2)*φ x) := by
  apply φ.integrable.norm.mono' (by unfold imaginaryExponential; fun_prop)
  filter_upwards with x
  have h := imaginaryExponential_derivative_norm 0 (β*x^2)
  simp only [iteratedDeriv_zero] at h
  rw [norm_mul,h,one_mul]

 theorem quadratic_taylor_integral_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ‖(∫ x, imaginaryExponential (β*x^2)*φ x) - (∫ x, imaginaryTaylor n (β*x^2)*φ x)‖ ≤
      (β^(n+1)/(n.factorial:ℝ)) * ∫ x : ℝ, ‖x‖^(2*(n+1))*‖φ x‖ := by
  rw [← integral_sub (imaginaryExponential_quadratic_integrable φ β)
    (imaginaryTaylor_quadratic_integrable φ n β),← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((φ.integrable_pow_mul volume (2*(n+1))).const_mul _) _
  filter_upwards with x
  rw [← sub_mul,norm_mul]
  have ht : 0 ≤ β*x^2 := mul_nonneg hβ (sq_nonneg x)
  calc
    _ ≤ ((β*x^2)^(n+1)/(n.factorial:ℝ))*‖φ x‖ :=
      mul_le_mul_of_nonneg_right (imaginaryExponential_taylor_bound n ht) (norm_nonneg _)
    _ = _ := by
      rw [Real.norm_eq_abs,pow_mul,sq_abs,mul_pow]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem schwartz_fourier_derivative_zero (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    iteratedDeriv n (fun x => 𝓕 φ x) 0 =
      (-2*(Real.pi:ℂ)*Complex.I)^n * ∫ x : ℝ, (x:ℂ)^n*φ x := by
  have hh := Real.iteratedDeriv_fourier (f := (φ : ℝ → ℂ)) (N := (⊤ : ℕ∞))
    (fun k _ => by simpa only [Complex.real_smul,Complex.ofReal_pow] using schwartz_monomial_integrable φ k) (n := n) (by simp)
  have hh := congrFun hh 0
  simp only [Real.fourier_eq,inner_zero_right,neg_zero,AddChar.map_zero_eq_one,one_smul,smul_eq_mul] at hh
  change iteratedDeriv n (fun x => 𝓕 φ x) 0 = _ at hh
  rw [hh]
  simp only [mul_pow,mul_assoc]
  simp_rw [integral_const_mul]

 theorem schwartz_inverse_moment (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ x : ℝ, (x:ℂ)^n*𝓕⁻ φ x) =
      ((-2*(Real.pi:ℂ)*Complex.I)^n)⁻¹ * iteratedDeriv n (φ : ℝ → ℂ) 0 := by
  have hh := schwartz_fourier_derivative_zero (𝓕⁻ φ) n
  simp only [FourierTransform.fourier_fourierInv_eq] at hh
  have hn : (-2*(Real.pi:ℂ)*Complex.I)^n ≠ 0 := pow_ne_zero _
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
  rw [hh,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_QuadraticStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem imaginaryTaylor_integral (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (β : ℝ) :
    (∫ x, imaginaryTaylor n (β*x^2)*φ x) =
      ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ∫ x : ℝ, (x:ℂ)^(2*k)*φ x := by
  have he : (fun x => imaginaryTaylor n (β*x^2)*φ x) =
      fun x : ℝ => ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ((x:ℂ)^(2*k)*φ x) := by
    funext x
    unfold imaginaryTaylor
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,mul_pow,pow_mul]
    ring
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact integral_const_mul _ _
  · intro k _
    exact (schwartz_monomial_integrable φ (2*k)).const_mul _

 theorem fresnelCoefficient_norm {b : ℝ} (hb : 0 < b) :
    ‖fresnelCoefficient b‖ = (Real.pi/b)^(1/2:ℝ) := by
  simp [fresnelCoefficient,Complex.norm_exp,Complex.mul_re,
    Complex.norm_real,abs_of_nonneg (Real.rpow_nonneg (div_pos Real.pi_pos hb).le _)]

 theorem quadratic_stationary_expansion {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    (Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : ℝ, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖ := by
  have he : (∫ x, imaginaryTaylor n ((Real.pi^2/b)*x^2)*𝓕⁻ φ x) = quadraticExpansion φ n b := by
    rw [imaginaryTaylor_integral]
    simp only [schwartz_inverse_moment,quadraticExpansion]
  have hex (ξ : ℝ) : Complex.exp (Complex.I*(((2*Real.pi*ξ:ℝ):ℂ)^2/(4*(b:ℂ)))) =
      imaginaryExponential ((Real.pi^2/b)*ξ^2) := by
    unfold imaginaryExponential
    congr 1
    push_cast
    ring
  rw [quadratic_stationary_identity hb φ]
  simp only [hex]
  change ‖fresnelCoefficient b * _ - fresnelCoefficient b * _‖ ≤ _
  rw [← mul_sub,norm_mul,fresnelCoefficient_norm hb,← he]
  have hh := quadratic_taylor_integral_bound (𝓕⁻ φ) n (div_nonneg (sq_nonneg Real.pi) hb.le)
  calc
    _ ≤ (Real.pi/b)^(1/2:ℝ) * (((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : ℝ, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SchwartzFourierMomentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace

 theorem schwartz_iteratedDeriv_integrable (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    Integrable (iteratedDeriv n (φ : ℝ → ℂ)) := by
  apply (φ.integrable_pow_mul_iteratedFDeriv volume 0 n).mono'
    ((φ.smooth ⊤).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).aestronglyMeasurable
  filter_upwards with x
  simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv]

 theorem schwartz_fourier_weighted_pointwise (φ : 𝓢(ℝ,ℂ)) (n : ℕ) (ξ : ℝ) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeL1 φ n := by
  have he := congrFun (Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k _ => schwartz_iteratedDeriv_integrable φ k) (n := n) (by simp)) ξ
  have hh := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) (iteratedDeriv n (φ : ℝ → ℂ)) ξ
  have hh' : ‖𝓕 (iteratedDeriv n (φ : ℝ → ℂ)) ξ‖ ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    simpa using! hh
  rw [he] at hh'
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,mul_one] at hh'
  have hh'' : (2*Real.pi)^n * (‖ξ‖^n*‖𝓕 φ ξ‖) ≤ ∫ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    convert hh' using 1
    all_goals try with_reducible_and_instances rfl
    simp only [mul_pow,Real.norm_eq_abs,SchwartzMap.fourier_coe]
    ring
  exact (le_div_iff₀ (by positivity : 0 < (2*Real.pi)^n)).mpr (by simpa [mul_comm] using hh'')

 theorem schwartz_fourier_moment_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ ξ : ℝ, ‖ξ‖^n*‖𝓕 φ ξ‖) ≤
      (fourierDerivativeL1 φ n + fourierDerivativeL1 φ (n+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹ := by
  have hi : Integrable (fun ξ : ℝ => ‖ξ‖^n*‖𝓕 φ ξ‖) := (𝓕 φ).integrable_pow_mul volume n
  rw [← integral_const_mul]
  apply integral_mono hi (integrable_inv_one_add_sq.const_mul _) _
  intro ξ
  have h₀ := schwartz_fourier_weighted_pointwise φ n ξ
  have h₂ := schwartz_fourier_weighted_pointwise φ (n+2) ξ
  have hp : 0 < 1+ξ^2 := by positivity
  dsimp only
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  have he : ‖ξ‖^(n+2)*‖𝓕 φ ξ‖ = (‖ξ‖^n*‖𝓕 φ ξ‖)*ξ^2 := by
    rw [pow_add,Real.norm_eq_abs,sq_abs]
    ring
  rw [he] at h₂
  nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_QuadraticStationaryL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem schwartz_inverse_fourier_moment_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ ξ : ℝ, ‖ξ‖^n*‖𝓕⁻ φ ξ‖) ≤
      (fourierDerivativeL1 φ n + fourierDerivativeL1 φ (n+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹ := by
  have hpoint (ξ : ℝ) : 𝓕⁻ φ ξ = 𝓕 φ (-ξ) := rfl
  simp_rw [hpoint]
  have he := integral_neg_eq_self (fun ξ : ℝ => ‖ξ‖^n*‖𝓕 φ ξ‖) volume
  simp only [norm_neg] at he
  rw [he]
  exact schwartz_fourier_moment_bound φ n

 theorem quadratic_stationary_expansion_L1 {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    ((Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
      ((fourierDerivativeL1 φ (2*(n+1)) + fourierDerivativeL1 φ (2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  apply (quadratic_stationary_expansion hb φ n).trans
  apply mul_le_mul_of_nonneg_left (schwartz_inverse_fourier_moment_bound φ (2*(n+1)))
  positivity

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactStationaryAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem complex_iteratedDeriv_tsupport (f : ℝ → ℂ) (n : ℕ) :
    tsupport (iteratedDeriv n f) ⊆ tsupport f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact (tsupport_deriv_subset).trans ih

 theorem compact_derivative_integral_bound (φ : 𝓢(ℝ,ℂ)) {a b C : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C) :
    (∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) ≤ C*(b-a) := by
  have he : (∫ x in Icc a b, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖) =
      ∫ x : ℝ, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply norm_eq_zero.mpr
    by_contra hn
    exact hx (hs (complex_iteratedDeriv_tsupport _ n (subset_closure hn)))
  have hh := norm_setIntegral_le_of_norm_le_const_ae (μ := volume)
    (f := fun x : ℝ => ‖iteratedDeriv n (φ : ℝ → ℂ) x‖)
    (s := Icc a b) (C := C) (by simp) (Filter.Eventually.of_forall (fun x => by simpa using hC x))
  rw [he,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hh
  simpa [Real.volume_Icc,Measure.real,ENNReal.toReal_ofReal,sub_nonneg.mpr hab] using hh

 theorem compact_fourierDerivativeL1_bound (φ : 𝓢(ℝ,ℂ)) {a b C D : ℝ}
    (hab : a ≤ b) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a b)
    (n : ℕ) (hC : ∀ x, ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ ≤ C*D^n) :
    fourierDerivativeL1 φ n ≤ C*(b-a)*D^n/(2*Real.pi)^n := by
  unfold fourierDerivativeL1
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (C*D^n)*(b-a) := compact_derivative_integral_bound φ hab hs n hC
    _ = _ := by ring

 theorem compact_smooth_to_schwartz {f : ℝ → ℂ} {a b : ℝ}
    (hs : tsupport f ⊆ Icc a b) (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = f := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  exact ⟨hc.toSchwartzMap hf,rfl⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineChart_inverse {u : ℝ} (hu : u ∈ Icc (-2:ℝ) 2) :
    stationarySineChart (stationarySineInverse u) = u := by
  unfold stationarySineChart stationarySineInverse
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    Real.sin_arcsin (by linarith [hu.1]) (by linarith [hu.2])]
  ring

 theorem stationarySineInverse_chart {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi) :
    stationarySineInverse (stationarySineChart θ) = θ := by
  unfold stationarySineChart stationarySineInverse
  rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),
    Real.arcsin_sin (by linarith [hθ.1]) (by linarith [hθ.2])]
  ring

 theorem stationarySineChart_cos (θ : ℝ) :
    Real.cos θ = 1 - (stationarySineChart θ)^2/2 := by
  have h := Real.cos_two_mul (θ/2)
  have hs := Real.sin_sq_add_cos_sq (θ/2)
  have he : 2*(θ/2) = θ := by ring
  rw [he] at h
  unfold stationarySineChart
  nlinarith

 theorem stationarySineInverse_cos {u : ℝ} (hu : u ∈ Icc (-2:ℝ) 2) :
    Real.cos (stationarySineInverse u) = 1 - u^2/2 := by
  rw [stationarySineChart_cos,stationarySineChart_inverse hu]

 theorem stationarySineInverse_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    HasDerivAt stationarySineInverse (stationarySineJacobian u) u := by
  have h := ((Real.hasDerivAt_arcsin (by linarith [hu.1] : u/2 ≠ -1)
    (by linarith [hu.2] : u/2 ≠ 1)).comp u ((hasDerivAt_id u).div_const 2)).const_mul 2
  have he : 1 - (u/2)^2 = 1 - u^2/4 := by ring
  have hc : 2 * (1 / Real.sqrt (1-(u/2)^2) * (1/2)) = stationarySineJacobian u := by
    rw [he]
    unfold stationarySineJacobian
    ring
  rw [hc] at h
  exact h

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

 theorem stationarySineJacobian_continuousOn :
    ContinuousOn stationarySineJacobian (Ioo (-2:ℝ) 2) := by
  apply ContinuousOn.inv₀
  · exact (Real.continuous_sqrt.comp (continuous_const.sub ((continuous_id.pow 2).div_const 4))).continuousOn
  · intro u hu
    apply ne_of_gt
    apply Real.sqrt_pos.2
    nlinarith [hu.1,hu.2,sq_nonneg (u-2),sq_nonneg (u+2)]

 theorem stationarySine_substitution {a b : ℝ} (ha : -2 < a) (hab : a ≤ b) (hb : b < 2)
    (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ u in a..b, (stationarySineJacobian u : ℂ) * f (stationarySineInverse u)) =
      ∫ θ in stationarySineInverse a..stationarySineInverse b, f θ := by
  have hs : uIcc a b ⊆ Ioo (-2:ℝ) 2 := by
    rw [uIcc_of_le hab]
    intro u hu
    exact ⟨ha.trans_le hu.1,hu.2.trans_lt hb⟩
  simpa only [Complex.real_smul,Function.comp_apply] using
    intervalIntegral.integral_deriv_smul_comp
      (fun u hu => stationarySineInverse_hasDerivAt (hs hu))
      (stationarySineJacobian_continuousOn.mono hs) hf

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

 theorem stationaryWeight_tsupport : tsupport stationaryWeight ⊆ Icc (-1:ℝ) 1 := by
  exact tsupport_mul_subset_left.trans stationaryCutoff_tsupport.subset

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SmoothCompositionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem compositionDerivativeCost_nonneg (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    0 ≤ compositionDerivativeCost g n x := by
  unfold compositionDerivativeCost
  positivity

 theorem compositionDerivativeCost_continuous {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (n : ℕ) : Continuous (compositionDerivativeCost g n) := by
  apply continuous_finsetSum
  intro c _
  apply continuous_finsetProd
  intro j _
  exact (hg.continuous_iteratedDeriv _ (by exact_mod_cast (le_top : (c.partSize j:ℕ∞) ≤ ⊤))).norm

 theorem composition_derivative_scale {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (f ∘ g) x‖ ≤ compositionDerivativeCost g n x * (C*D^n) := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt hg.contDiffAt
    (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))]
  rw [compositionDerivativeCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  rw [norm_smul, norm_prod]
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
  exact (hb c.length c.length_le).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD c.length_le) hC)

 theorem weightedCompositionCost_continuous {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    Continuous (weightedCompositionCost w g n) := by
  apply continuous_finsetSum
  intro k _
  exact (continuous_const.mul (hw.continuous_iteratedDeriv k
    (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).norm).mul
      (compositionDerivativeCost_continuous hg (n-k))

 theorem weighted_composition_derivative_scale {w f : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n, ‖iteratedDeriv k f (g x)‖ ≤ C*D^k) :
    ‖iteratedDeriv n (fun x => w x * f (g x)) x‖ ≤
      weightedCompositionCost w g n x * (C*D^n) := by
  have hwn : ContDiffAt ℝ n w x := (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hfn : ContDiffAt ℝ n (f ∘ g) x :=
    ((hf.comp hg).of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change ‖iteratedDeriv n (fun y => w y * (f ∘ g) y) x‖ ≤ _
  rw [iteratedDeriv_fun_mul hwn hfn,weightedCompositionCost,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  simp only [norm_mul,Complex.norm_natCast]
  have hc := composition_derivative_scale hf hg hC hD (n-k) x
    (fun l hl => hb l (hl.trans (Nat.sub_le _ _)))
  have hp : C*D^(n-k) ≤ C*D^n :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.sub_le _ _)) hC
  calc
    _ ≤ (n.choose k:ℝ) * ‖iteratedDeriv k w x‖ *
        (compositionDerivativeCost g (n-k) x * (C*D^n)) := by
      gcongr
      exact hc.trans (mul_le_mul_of_nonneg_left hp (compositionDerivativeCost_nonneg _ _ _))
    _ = _ := by ring

 theorem compact_weighted_composition_scale {w : ℝ → ℂ} {g : ℝ → ℝ}
    (hw : ContDiff ℝ ∞ w) (hg : ContDiff ℝ ∞ g)
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (f : ℝ → ℂ), ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖iteratedDeriv n (fun y => w y * f (g y)) x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (weightedCompositionCost_continuous hw hg n).continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hA : weightedCompositionCost w g n x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  calc
    _ ≤ weightedCompositionCost w g n x * (C*D^n) :=
      weighted_composition_derivative_scale hw hf hg hC hD n x (fun k hk => hb k hk _)
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartAmplitude
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff SchwartzMap

 theorem stationaryAmplitude_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) (f : ℝ → ℂ) :
    stationaryAmplitude f u =
      (stationarySineJacobian u : ℂ) * (stationaryCutoff u : ℂ) * f (stationarySineInverse u) := by
  simp only [stationaryAmplitude,stationaryWeight,Complex.ofReal_mul,extendedStationaryInverse_eq hu]
  ring

 theorem stationaryAmplitude_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (stationaryAmplitude f) := by
  exact (Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff).mul
    (hf.comp extendedStationaryInverse_contDiff)

 theorem stationaryAmplitude_tsupport (f : ℝ → ℂ) :
    tsupport (stationaryAmplitude f) ⊆ Icc (-1:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have hw : stationaryWeight x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hn (stationaryWeight_tsupport h))
  exact hx (by simp [stationaryAmplitude,hw])

 theorem stationaryAmplitude_uniform_derivatives (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f →
      ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ y, ‖iteratedDeriv k f y‖ ≤ C*D^k) →
      ∀ x, ‖iteratedDeriv n (stationaryAmplitude f) x‖ ≤ A*C*D^n := by
  obtain ⟨A,hA,hbound⟩ := compact_weighted_composition_scale
    (Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff)
    extendedStationaryInverse_contDiff (K := Icc (-1:ℝ) 1) isCompact_Icc n
  refine ⟨A,hA,?_⟩
  intro f hf C D hC hD hb x
  by_cases hx : x ∈ Icc (-1:ℝ) 1
  · exact hbound f hf C D hC hD hb x hx
  · have he : iteratedDeriv n (stationaryAmplitude f) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx
        (stationaryAmplitude_tsupport f (complex_iteratedDeriv_tsupport _ n hh)))
    rw [he,norm_zero]
    positivity

 theorem stationaryAmplitude_schwartz {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ∃ φ : 𝓢(ℝ,ℂ), (φ : ℝ → ℂ) = stationaryAmplitude f :=
  compact_smooth_to_schwartz (stationaryAmplitude_tsupport f) (stationaryAmplitude_contDiff hf)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationaryAmplitude_support (f : ℝ → ℂ) :
    Function.support (stationaryAmplitude f) ⊆ Ioo (-1:ℝ) 1 := by
  intro u hu
  have hw : stationaryCutoff u ≠ 0 := by
    intro h
    exact hu (by simp [stationaryAmplitude,stationaryWeight,h])
  have hh : u ∈ Metric.ball (0:ℝ) 1 := by
    change u ∈ Function.support (stationaryCutoff : ℝ → ℝ) at hw
    rw [ContDiffBump.support_eq] at hw
    exact hw
  simpa [Real.ball_eq_Ioo] using hh

 theorem localizedCircleIntegral_quadratic (Λ : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    localizedCircleIntegral Λ f = Complex.exp (Complex.I*(Λ:ℂ)) *
      ∫ u : ℝ, Complex.exp (-(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2) * stationaryAmplitude f u := by
  let F : ℝ → ℂ := fun θ => Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos θ:ℂ)) *
    (stationaryCutoff (stationarySineChart θ) : ℂ) * f θ
  have hchart : Continuous stationarySineChart := by
    unfold stationarySineChart
    fun_prop
  have hF : Continuous F := by
    apply Continuous.mul _ hf
    apply Continuous.mul
    · exact Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos))
    · exact Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hchart)
  change (∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, F θ) = _
  rw [← stationarySine_substitution (by norm_num : (-2:ℝ) < -1) (by norm_num) (by norm_num) F hF]
  have he : (∫ u in (-1:ℝ)..1, (stationarySineJacobian u : ℂ)*F (stationarySineInverse u)) =
      ∫ u in (-1:ℝ)..1, Complex.exp (Complex.I*(Λ:ℂ)) *
        (Complex.exp (-(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2)*stationaryAmplitude f u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (-1:ℝ) 1 := by simpa using hu
    have hu2 : u ∈ Icc (-2:ℝ) 2 := ⟨by linarith [hu'.1],by linarith [hu'.2]⟩
    dsimp [F]
    rw [stationarySineInverse_cos hu2,stationarySineChart_inverse hu2,
      stationaryAmplitude_eq hu']
    have hp : Complex.I*(Λ:ℂ)*((1-u^2/2:ℝ):ℂ) =
        Complex.I*(Λ:ℂ) + -(((Λ/2:ℝ):ℂ)*Complex.I)*(u:ℂ)^2 := by
      push_cast
      ring
    rw [hp,Complex.exp_add]
    ring
  rw [he,intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have hs : u ∈ Ioo (-1:ℝ) 1 := stationaryAmplitude_support f (by
    intro h
    exact hu (by simp [h]))
  exact ⟨hs.1,hs.2.le⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_CompactQuadraticExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped SchwartzMap ContDiff

 theorem compact_quadratic_stationary_expansion {b a z C D : ℝ} (hb : 0 < b)
    (haz : a ≤ z) (φ : 𝓢(ℝ,ℂ)) (hs : tsupport (φ : ℝ → ℂ) ⊆ Icc a z) (n : ℕ)
    (h₀ : ∀ x, ‖iteratedDeriv (2*(n+1)) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)))
    (h₂ : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)+2)) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    ((Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
      ((C*(z-a)*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
        C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  apply (quadratic_stationary_expansion_L1 hb φ n).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun _ => by positivity))
  exact add_le_add (compact_fourierDerivativeL1_bound φ haz hs _ h₀)
    (compact_fourierDerivativeL1_bound φ haz hs _ h₂)

 theorem compact_quadratic_derivative_scale {a z C D : ℝ} (haz : a ≤ z)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (n : ℕ) :
    C*(z-a)*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
      C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2) ≤
    (C*(z-a)*((2*Real.pi)^(2*(n+1)))⁻¹ +
      C*(z-a)*((2*Real.pi)^(2*(n+1)+2))⁻¹) * D^(2*(n+1)+2) := by
  have hp : D^(2*(n+1)) ≤ D^(2*(n+1)+2) := pow_le_pow_right₀ hD (by omega)
  calc
    _ ≤ C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)) +
      C*(z-a)*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2) := by
      exact add_le_add
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sub_nonneg.mpr haz)))
          (show 0 ≤ (2 * Real.pi) ^ (2 * (n + 1)) by positivity)) le_rfl
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_LocalizedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem localized_stationary_expansion {Λ C D : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (h₀ : ∀ x, ‖iteratedDeriv (2*(n+1)) (stationaryAmplitude f) x‖ ≤ C*D^(2*(n+1)))
    (h₂ : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (stationaryAmplitude f) x‖ ≤ C*D^(2*(n+1)+2)) :
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      ((C*2*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
        C*2*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  obtain ⟨φ,hφ⟩ := stationaryAmplitude_schwartz hf
  have hs : tsupport (φ : ℝ → ℂ) ⊆ Icc (-1:ℝ) 1 := by
    rw [hφ]
    exact stationaryAmplitude_tsupport f
  have h₀' : ∀ x, ‖iteratedDeriv (2*(n+1)) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)) := by simpa [hφ] using h₀
  have h₂' : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)+2) := by simpa [hφ] using h₂
  have hh := compact_quadratic_stationary_expansion (half_pos hΛ) (by norm_num : (-1:ℝ) ≤ 1)
    φ hs n h₀' h₂'
  have he : quadraticExpansion φ n (Λ/2) = stationaryDerivativeExpansion f n Λ := by
    unfold quadraticExpansion stationaryDerivativeExpansion
    rw [hφ]
  have hn : ‖Complex.exp (Complex.I*(Λ:ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [localizedCircleIntegral_quadratic Λ hf.continuous,← mul_sub,norm_mul,hn,one_mul]
  have hφ' : ∀ x, φ x = stationaryAmplitude f x := congrFun hφ
  simpa only [hφ',he,show (1:ℝ)- -1 = 2 by norm_num] using hh

 theorem localized_stationary_uniform_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      (A*C*D^(2*(n+1)+2)) := by
  obtain ⟨A₀,hA₀,h₀⟩ := stationaryAmplitude_uniform_derivatives (2*(n+1))
  obtain ⟨A₂,hA₂,h₂⟩ := stationaryAmplitude_uniform_derivatives (2*(n+1)+2)
  let B := max A₀ A₂
  let V : ℝ := ∫ ξ : ℝ, (1+ξ^2)⁻¹
  let A : ℝ := (B*2*((2*Real.pi)^(2*(n+1)))⁻¹ + B*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*V
  have hB : 0 ≤ B := hA₀.trans (le_max_left _ _)
  have hV : 0 ≤ V := integral_nonneg (fun _ => by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro f hf Λ C D hΛ hC hD hb
  have hD_nonneg : 0 ≤ D := zero_le_one.trans hD
  have hb₀ (x : ℝ) : ‖iteratedDeriv (2*(n+1)) (stationaryAmplitude f) x‖ ≤ (B*C)*D^(2*(n+1)) :=
    (h₀ f hf C D hC hD (fun k hk => hb k (by omega)) x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left A₀ A₂) hC) (pow_nonneg hD_nonneg _))
  have hb₂ (x : ℝ) : ‖iteratedDeriv (2*(n+1)+2) (stationaryAmplitude f) x‖ ≤ (B*C)*D^(2*(n+1)+2) :=
    (h₂ f hf C D hC hD hb x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right A₀ A₂) hC) (pow_nonneg hD_nonneg _))
  apply (localized_stationary_expansion hΛ hf n hb₀ hb₂).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := compact_quadratic_derivative_scale (by norm_num : (-1:ℝ) ≤ 1)
    (mul_nonneg hB hC) hD n
  have he : ((B*C)*2*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
      (B*C)*2*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) ≤
      ((B*C)*2*((2*Real.pi)^(2*(n+1)))⁻¹ +
      (B*C)*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*D^(2*(n+1)+2) := by
    simpa only [show (1:ℝ)- -1 = 2 by norm_num] using hh
  calc
    _ ≤ (((B*C)*2*((2*Real.pi)^(2*(n+1)))⁻¹ +
        (B*C)*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*D^(2*(n+1)+2))*V :=
      mul_le_mul_of_nonneg_right he hV
    _ = _ := by dsimp [A]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryOppositePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_iteratedDeriv_conj {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => conj (f x)) = fun x => conj (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt (x := x)
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    change HasDerivAt (fun y => conj (iteratedDeriv n f y))
      (conj (deriv (iteratedDeriv n f) x)) x at hh
    simpa only [iteratedDeriv_succ] using hh.deriv

 theorem localizedCircleIntegral_neg (Λ : ℝ) (f : ℝ → ℂ) :
    localizedCircleIntegral (-Λ) f = conj (localizedCircleIntegral Λ (fun x => conj (f x))) := by
  unfold localizedCircleIntegral intervalIntegral
  rw [map_sub,← integral_conj,← integral_conj]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards with θ
  all_goals
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj,← Complex.exp_conj,
      Complex.conj_I,Complex.ofReal_neg]
    congr 2
    ring_nf

 theorem localized_stationary_opposite_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral (-Λ) f -
      conj (Complex.exp (Complex.I*(Λ:ℂ)) * (fresnelCoefficient (Λ/2) *
        stationaryDerivativeExpansion (fun x => conj (f x)) n Λ))‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      (A*C*D^(2*(n+1)+2)) := by
  obtain ⟨A,hA,hh⟩ := localized_stationary_uniform_remainder n
  refine ⟨A,hA,?_⟩
  intro f hf Λ C D hΛ hC hD hb
  have hf' : ContDiff ℝ ∞ (fun x => conj (f x)) := Complex.conjCLE.contDiff.comp hf
  have hb' : ∀ k ≤ 2*(n+1)+2, ∀ x,
      ‖iteratedDeriv k (fun x => conj (f x)) x‖ ≤ C*D^k := by
    intro k hk x
    rw [complex_iteratedDeriv_conj hf]
    simpa only [Complex.norm_conj] using hb k hk x
  rw [localizedCircleIntegral_neg,← map_sub,Complex.norm_conj]
  exact hh hf' hΛ hC hD hb'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularIntegrationByParts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem cosineOscillator_hasDerivAt (Λ x : ℝ) :
    HasDerivAt (cosineOscillator Λ)
      (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) x := by
  have h := (((Real.hasDerivAt_cos x).ofReal_comp).const_mul (Complex.I*(Λ:ℂ))).cexp
  have he : Complex.exp (Complex.I*(Λ:ℂ)*(Real.cos x:ℂ)) *
      (Complex.I*(Λ:ℂ)*(-Real.sin x:ℝ)) =
        -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x := by
    simp only [cosineOscillator,Complex.ofReal_neg]
    ring
  rw [he] at h
  exact h

 theorem cosineOscillator_continuous (Λ : ℝ) : Continuous (cosineOscillator Λ) :=
  continuous_iff_continuousAt.mpr (fun x => (cosineOscillator_hasDerivAt Λ x).continuousAt)

 theorem cosineOscillator_norm (Λ x : ℝ) : ‖cosineOscillator Λ x‖ = 1 := by
  simp [cosineOscillator,Complex.norm_exp]

 theorem angular_integration_by_parts {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) =
      (Complex.I*(Λ:ℂ)) * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  let v : ℝ → ℂ := fun x => q x * f x
  have hv : ContDiff ℝ ∞ v := hq.mul hf
  have hvc : HasCompactSupport v := hc.mul_left
  have hE := cosineOscillator_continuous Λ
  have hv' : Continuous (angularTransport q f) := hv.continuous_deriv (by simp)
  have hi₁ : Integrable (fun x => cosineOscillator Λ x * angularTransport q f x) :=
    (hE.mul hv').integrable_of_hasCompactSupport hvc.deriv.mul_left
  have hE' : Continuous (fun x => -Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_sin)).mul hE
  have hi₂ : Integrable (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) :=
    (hE'.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hi₃ : Integrable (fun x => cosineOscillator Λ x * v x) :=
    (hE.mul hv.continuous).integrable_of_hasCompactSupport hvc.mul_left
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := cosineOscillator Λ) (v := v) (v' := angularTransport q f)
    (fun x _ => cosineOscillator_hasDerivAt Λ x)
    (fun x _ => (hv.differentiable (by simp)).differentiableAt.hasDerivAt) hi₁ hi₂ hi₃
  change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q f x) = _ at hh
  rw [hh]
  have he : (fun x => (-Complex.I*(Λ:ℂ)*(Real.sin x:ℂ)*cosineOscillator Λ x)*v x) =
      fun x => -(Complex.I*(Λ:ℂ)) * (cosineOscillator Λ x * f x) := by
    funext x
    by_cases hx : x ∈ tsupport f
    · dsimp [v]
      calc
        _ = -(Complex.I*(Λ:ℂ)) * cosineOscillator Λ x * ((Real.sin x:ℂ)*q x) * f x := by ring
        _ = _ := by rw [hqs x hx]; ring
    · simp [v,image_eq_zero_of_notMem_tsupport hx]
  rw [he,integral_const_mul]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularTransportBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem angularTransportIterate_contDiff {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (angularTransportIterate q n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact (contDiff_infty_iff_deriv.mp (hq.mul ih)).2

 theorem angularTransportIterate_support (q f : ℝ → ℂ) (n : ℕ) :
    tsupport (angularTransportIterate q n f) ⊆ tsupport f := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact tsupport_deriv_subset.trans (tsupport_mul_subset_right.trans ih)

 theorem angularTransportCost_nonneg (q : ℝ → ℂ) (n m : ℕ) (x : ℝ) :
    0 ≤ angularTransportCost q n m x := by
  induction n generalizing m with
  | zero => exact zero_le_one
  | succ n ih =>
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (ih _)

 theorem angularTransportCost_continuous {q : ℝ → ℂ} (hq : ContDiff ℝ ∞ q) (n m : ℕ) :
    Continuous (angularTransportCost q n m) := by
  induction n generalizing m with
  | zero => exact continuous_const
  | succ n ih =>
    apply continuous_finsetSum
    intro k _
    exact (continuous_const.mul (hq.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr (show (k:ℕ∞) ≤ ⊤ from le_top))).norm).mul (ih _)

 theorem angularTransportIterate_derivative_bound {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (n m : ℕ) (x : ℝ)
    (hb : ∀ k ≤ n+m, ‖iteratedDeriv k f x‖ ≤ C*D^k) :
    ‖iteratedDeriv m (angularTransportIterate q n f) x‖ ≤
      angularTransportCost q n m x * (C*D^(n+m)) := by
  induction n generalizing m with
  | zero => simpa [angularTransportIterate,angularTransportCost] using hb m (by omega)
  | succ n ih =>
    have hqn : ContDiffAt ℝ (m+1:ℕ) q x :=
      (hq.of_le (WithTop.coe_le_coe.mpr (show ((m+1:ℕ):ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    have hin : ContDiffAt ℝ (m+1:ℕ) (angularTransportIterate q n f) x :=
      ((angularTransportIterate_contDiff hq hf n).of_le (WithTop.coe_le_coe.mpr (show ((m+1:ℕ):ℕ∞) ≤ ⊤ from le_top))).contDiffAt
    change ‖iteratedDeriv m (deriv (fun y => q y * angularTransportIterate q n f y)) x‖ ≤ _
    rw [← iteratedDeriv_succ',iteratedDeriv_fun_mul hqn hin]
    change ‖_‖ ≤ (∑ k ∈ Finset.range (m+2), _) * _
    rw [Finset.sum_mul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    simp only [norm_mul,Complex.norm_natCast]
    have hl : n+(m+1-k) ≤ n+1+m := by omega
    have hh := ih (m+1-k) (fun j hj => hb j (hj.trans hl))
    have hp : C*D^(n+(m+1-k)) ≤ C*D^(n+1+m) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hl) hC
    calc
      _ ≤ ((m+1).choose k:ℝ) * ‖iteratedDeriv k q x‖ *
          (angularTransportCost q n (m+1-k) x * (C*D^(n+1+m))) := by
        gcongr
        exact hh.trans (mul_le_mul_of_nonneg_left hp (angularTransportCost_nonneg _ _ _ _))
      _ = _ := by ring

 theorem angularTransportIterate_uniform_bound {q : ℝ → ℂ} (hq : ContDiff ℝ ∞ q)
    {K : Set ℝ} (hK : IsCompact K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      ∀ {C D : ℝ}, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ∀ x ∈ K, ‖angularTransportIterate q n f x‖ ≤ A*C*D^n := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (angularTransportCost_continuous hq n 0).continuousOn
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro f hf C D hC hD hb x hx
  have hh := angularTransportIterate_derivative_bound hq hf hC hD n 0 x (by simpa using fun k hk => hb k hk x)
  simp only [iteratedDeriv_zero,Nat.add_zero] at hh
  have hA : angularTransportCost q n 0 x ≤ max 0 B :=
    (le_abs_self _).trans ((hB x hx).trans (le_max_right _ _))
  apply hh.trans
  calc
    _ ≤ max 0 B * (C*D^n) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothInverseSine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem smoothInverseSine_contDiff (η : ℝ) (hη : 0 < η) :
    ContDiff ℝ ∞ (smoothInverseSine η hη) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Real.sin x = 0
  · have hb : (sineZeroCutoff η hη : ℝ → ℝ) =ᶠ[𝓝 (Real.sin x)] (fun _ => 1) := by
      rw [hx]
      exact (sineZeroCutoff η hη).eventuallyEq_one
    have he : smoothInverseSine η hη =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hb.comp_tendsto Real.continuous_sin.continuousAt] with y hy
      simp only [Function.comp_apply] at hy
      simp [smoothInverseSine,hy]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hb : ContDiffAt ℝ ∞ (fun y => sineZeroCutoff η hη (Real.sin y)) x :=
      (sineZeroCutoff η hη).contDiffAt.comp x Real.contDiff_sin.contDiffAt
    exact (contDiffAt_const.sub hb).mul (Real.contDiff_sin.contDiffAt.inv hx)

 theorem smoothInverseSine_eq {η : ℝ} (hη : 0 < η) {θ : ℝ}
    (hθ : η ≤ |Real.sin θ|) : (Real.sin θ)*smoothInverseSine η hη θ = 1 := by
  have hb : sineZeroCutoff η hη (Real.sin θ) = 0 :=
    (sineZeroCutoff η hη).zero_of_le_dist (by simpa [sineZeroCutoff,Real.dist_eq] using hθ)
  have hs : Real.sin θ ≠ 0 := by intro he; simp [he] at hθ; linarith
  simp [smoothInverseSine,hb,hs]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularNonstationary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

 theorem angularTransportIterate_integral {q f : ℝ → ℂ}
    (hq : ContDiff ℝ ∞ q) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1) (Λ : ℝ) (n : ℕ) :
    (∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x) =
      (Complex.I*(Λ:ℂ))^n * ∫ x : ℝ, cosineOscillator Λ x * f x := by
  induction n with
  | zero => simp [angularTransportIterate]
  | succ n ih =>
    have hi := angularTransportIterate_contDiff hq hf n
    have hc' : HasCompactSupport (angularTransportIterate q n f) :=
      hc.mono' (fun x hx => angularTransportIterate_support q f n (subset_closure hx))
    have hh := angular_integration_by_parts hq hi hc'
      (fun x hx => hqs x (angularTransportIterate_support q f n hx)) Λ
    change (∫ x : ℝ, cosineOscillator Λ x * angularTransport q (angularTransportIterate q n f) x) = _
    rw [hh,ih,pow_succ]
    ring

 theorem angular_nonstationary_uniform {η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    tsupport f ⊆ Icc a b → (∀ x ∈ tsupport f, η ≤ |Real.sin x|) →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ ≤ A*C*D^n/Λ^n := by
  let q : ℝ → ℂ := fun x => (smoothInverseSine η hη x : ℂ)
  have hq : ContDiff ℝ ∞ q := Complex.ofRealCLM.contDiff.comp (smoothInverseSine_contDiff η hη)
  obtain ⟨A,hA,hbound⟩ := angularTransportIterate_uniform_bound hq (K := Icc a b) isCompact_Icc n
  refine ⟨A*(b-a),mul_nonneg hA (sub_nonneg.mpr hab),?_⟩
  intro f hf hs haway C D Λ hC hD hΛ hb
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hs
  have hqs : ∀ x ∈ tsupport f, (Real.sin x:ℂ)*q x = 1 := by
    intro x hx
    change (Real.sin x:ℂ)*(smoothInverseSine η hη x:ℂ) = 1
    exact_mod_cast smoothInverseSine_eq hη (haway x hx)
  have hit := angularTransportIterate_contDiff hq hf n
  have hist : tsupport (angularTransportIterate q n f) ⊆ Icc a b :=
    (angularTransportIterate_support q f n).trans hs
  have hib : ∀ x, ‖angularTransportIterate q n f x‖ ≤ A*C*D^n := by
    intro x
    by_cases hx : x ∈ Icc a b
    · exact hbound hf hC hD hb x hx
    · rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hist hh)),norm_zero]
      positivity
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hist hit
  have hsφ : tsupport (φ : ℝ → ℂ) ⊆ Icc a b := by simpa [hφ] using hist
  have hbφ : ∀ x, ‖iteratedDeriv 0 (φ : ℝ → ℂ) x‖ ≤ A*C*D^n := by simpa [hφ] using hib
  have hL := compact_derivative_integral_bound φ hab hsφ 0 hbφ
  simp only [iteratedDeriv_zero] at hL
  have hφ' : ∀ x, φ x = angularTransportIterate q n f x := congrFun hφ
  simp only [hφ'] at hL
  have hi : ‖∫ x : ℝ, cosineOscillator Λ x * angularTransportIterate q n f x‖ ≤
      (A*C*D^n)*(b-a) := by
    apply (norm_integral_le_integral_norm _).trans
    simpa only [norm_mul,cosineOscillator_norm,one_mul] using hL
  rw [angularTransportIterate_integral hq hf hc hqs Λ n,norm_mul,norm_pow,norm_mul,
    Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hΛ] at hi
  apply (le_div_iff₀ (pow_pos hΛ n)).mpr
  calc
    _ = Λ^n * ‖∫ x : ℝ, cosineOscillator Λ x * f x‖ := by ring
    _ ≤ (A*C*D^n)*(b-a) := hi
    _ = _ := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleStationaryPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationary_charts_sq (θ : ℝ) :
    stationarySineChart θ^2 + stationaryCosineChart θ^2 = 4 := by
  have h := Real.sin_sq_add_cos_sq (θ/2)
  unfold stationarySineChart stationaryCosineChart
  nlinarith

 theorem stationary_charts_product (θ : ℝ) :
    stationarySineChart θ * stationaryCosineChart θ = 2*Real.sin θ := by
  have h := Real.sin_two_mul (θ/2)
  rw [show 2*(θ/2)=θ by ring] at h
  unfold stationarySineChart stationaryCosineChart
  nlinarith

 theorem stationaryCutoff_one_of_abs_le {u : ℝ} (hu : |u| ≤ 1/2) : stationaryCutoff u = 1 := by
  exact stationaryCutoff.one_of_mem_closedBall (by simpa [stationaryCutoff,Real.dist_eq] using hu)

 theorem stationaryCutoff_zero_of_abs_le {u : ℝ} (hu : 1 ≤ |u|) : stationaryCutoff u = 0 := by
  exact stationaryCutoff.zero_of_le_dist (by simpa [stationaryCutoff,Real.dist_eq] using hu)

 theorem circleStationaryResidual_zero_sine {θ : ℝ} (hθ : |stationarySineChart θ| ≤ 1/2) :
    circleStationaryResidual θ = 0 := by
  have h := stationary_charts_sq θ
  have hv : 1 ≤ |stationaryCosineChart θ| := by
    nlinarith [sq_abs (stationarySineChart θ),sq_abs (stationaryCosineChart θ),
      abs_nonneg (stationarySineChart θ),abs_nonneg (stationaryCosineChart θ)]
  simp [circleStationaryResidual,stationaryCutoff_one_of_abs_le hθ,stationaryCutoff_zero_of_abs_le hv]

 theorem circleStationaryResidual_zero_cosine {θ : ℝ} (hθ : |stationaryCosineChart θ| ≤ 1/2) :
    circleStationaryResidual θ = 0 := by
  have h := stationary_charts_sq θ
  have hv : 1 ≤ |stationarySineChart θ| := by
    nlinarith [sq_abs (stationarySineChart θ),sq_abs (stationaryCosineChart θ),
      abs_nonneg (stationarySineChart θ),abs_nonneg (stationaryCosineChart θ)]
  simp [circleStationaryResidual,stationaryCutoff_one_of_abs_le hθ,stationaryCutoff_zero_of_abs_le hv]

 theorem circleStationaryResidual_support :
    tsupport circleStationaryResidual ⊆ {θ : ℝ | (1:ℝ)/8 ≤ |Real.sin θ|} := by
  apply closure_minimal
  · intro θ hθ
    have hu : 1/2 < |stationarySineChart θ| := lt_of_not_ge (fun hh => hθ (circleStationaryResidual_zero_sine hh))
    have hv : 1/2 < |stationaryCosineChart θ| := lt_of_not_ge (fun hh => hθ (circleStationaryResidual_zero_cosine hh))
    have he := congrArg abs (stationary_charts_product θ)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
    dsimp
    nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hv)]
  · exact isClosed_le continuous_const Real.continuous_sin.abs

 theorem circleStationaryResidual_contDiff : ContDiff ℝ ∞ circleStationaryResidual := by
  have hs : ContDiff ℝ ∞ stationarySineChart := by unfold stationarySineChart; fun_prop
  have hc : ContDiff ℝ ∞ stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  exact (contDiff_const.sub (stationaryCutoff.contDiff.comp hs)).sub (stationaryCutoff.contDiff.comp hc)

 theorem circleStationaryResidual_eventually_zero {θ : ℝ} (hθ : Real.cos (θ/2) = 0) :
    circleStationaryResidual =ᶠ[𝓝 θ] (fun _ => 0) := by
  have hc : Continuous stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  have he : stationaryCosineChart θ = 0 := by simp [stationaryCosineChart,hθ]
  have hn : ∀ᶠ x in 𝓝 θ, |stationaryCosineChart x| < 1/2 := by
    exact hc.abs.continuousAt.eventually (gt_mem_nhds (by simp [he]))
  filter_upwards [hn] with x hx
  exact circleStationaryResidual_zero_cosine hx.le

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleLocalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineInverse_mem (u : ℝ) :
    stationarySineInverse u ∈ Icc (-Real.pi) Real.pi := by
  unfold stationarySineInverse
  constructor
  · linarith [Real.neg_pi_div_two_le_arcsin (u/2)]
  · linarith [Real.arcsin_le_pi_div_two (u/2)]

 theorem stationarySineInverse_mono : Monotone stationarySineInverse := by
  intro a b hab
  unfold stationarySineInverse
  have h := Real.arcsin_le_arcsin (show a/2 ≤ b/2 by linarith)
  linarith

 theorem stationaryCutoff_angle_support {θ : ℝ} (hθ : θ ∈ Icc (-Real.pi) Real.pi)
    (hc : stationaryCutoff (stationarySineChart θ) ≠ 0) :
    θ ∈ Ioo (stationarySineInverse (-1)) (stationarySineInverse 1) := by
  have hh : stationarySineChart θ ∈ Function.support (stationaryCutoff : ℝ → ℝ) := hc
  rw [ContDiffBump.support_eq] at hh
  have hu : |stationarySineChart θ| < 1 := by simpa [stationaryCutoff,Real.dist_eq] using hh
  have ha := Real.arcsin_lt_arcsin (by norm_num : (-1:ℝ) ≤ -1/2)
    (show (-1:ℝ)/2 < stationarySineChart θ/2 by linarith [(abs_lt.mp hu).1])
    (show stationarySineChart θ/2 ≤ 1 by linarith [(abs_lt.mp hu).2])
  have hb := Real.arcsin_lt_arcsin
    (show (-1:ℝ) ≤ stationarySineChart θ/2 by linarith [(abs_lt.mp hu).1])
    (show stationarySineChart θ/2 < (1:ℝ)/2 by linarith [(abs_lt.mp hu).2]) (by norm_num)
  have he := stationarySineInverse_chart hθ
  unfold stationarySineInverse at he ⊢
  constructor <;> linarith

 theorem circlePositivePiece_localized (Λ : ℝ) (f : ℝ → ℂ) :
    circlePositivePiece Λ f = localizedCircleIntegral Λ f := by
  let F : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ
  let P : ℝ → ℂ := (Ioc (-Real.pi) Real.pi).indicator F
  have hP : Function.support P ⊆ Ioc (stationarySineInverse (-1)) (stationarySineInverse 1) := by
    intro θ hθ
    have ht : θ ∈ Ioc (-Real.pi) Real.pi := by
      by_contra hh
      exact hθ (indicator_of_notMem hh F)
    have hc : stationaryCutoff (stationarySineChart θ) ≠ 0 := by
      intro hh
      exact hθ (by simp [P,F,ht,hh])
    have h := stationaryCutoff_angle_support ⟨ht.1.le,ht.2⟩ hc
    exact ⟨h.1,h.2.le⟩
  have he : (∫ θ : ℝ, P θ) = circlePositivePiece Λ f := by
    rw [integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)).symm
  rw [← he,← intervalIntegral.integral_eq_integral_of_support_subset hP]
  change (∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, P θ) =
    ∫ θ in stationarySineInverse (-1)..stationarySineInverse 1, F θ
  apply intervalIntegral.integral_congr_ae
  filter_upwards with θ hθ
  have hθ' : θ ∈ Ioc (stationarySineInverse (-1)) (stationarySineInverse 1) := by
    simpa only [uIoc_of_le (stationarySineInverse_mono (by norm_num : (-1:ℝ) ≤ 1))] using hθ
  have ht : θ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨(stationarySineInverse_mem (-1)).1.trans_lt hθ'.1,hθ'.2.trans (stationarySineInverse_mem 1).2⟩
  exact indicator_of_mem ht F

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CompactCircleResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff Topology

 theorem contDiff_interval_zero_extension {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ ∞ f)
    (ha : f =ᶠ[𝓝 a] (fun _ => 0)) (hb : f =ᶠ[𝓝 b] (fun _ => 0)) :
    ContDiff ℝ ∞ ((Ioo a b).indicator f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo a b
  · apply hf.contDiffAt.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact indicator_of_mem hy f
  · have he : (Ioo a b).indicator f =ᶠ[𝓝 x] (fun _ => 0) := by
      by_cases hc : x ∈ Icc a b
      · have hab : x = a ∨ x = b := by
          simp only [mem_Ioo,not_and_or,not_lt] at hx
          rcases hx with hx | hx
          · exact Or.inl (le_antisymm hx hc.1)
          · exact Or.inr (le_antisymm hc.2 hx)
        have hh : f =ᶠ[𝓝 x] (fun _ => 0) := by rcases hab with rfl | rfl; exact ha; exact hb
        filter_upwards [hh] with y hy
        by_cases hy' : y ∈ Ioo a b <;> simp [hy',hy]
      · filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hc] with y hy
        have hy' : y ∉ Ioo a b := fun hh => hy (Ioo_subset_Icc_self hh)
        exact indicator_of_notMem hy' f
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem compactCircleResidual_contDiff : ContDiff ℝ ∞ compactCircleResidual := by
  apply contDiff_interval_zero_extension circleStationaryResidual_contDiff
  · apply circleStationaryResidual_eventually_zero
    rw [neg_div,Real.cos_neg,Real.cos_pi_div_two]
  · exact circleStationaryResidual_eventually_zero Real.cos_pi_div_two

 theorem compactCircleResidual_tsupport :
    tsupport compactCircleResidual ⊆ Icc (-Real.pi) Real.pi := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have hx' : x ∉ Ioo (-Real.pi) Real.pi := fun hh => hn (Ioo_subset_Icc_self hh)
  exact hx (indicator_of_notMem hx' _)

 theorem compactCircleResidual_sine_support :
    tsupport compactCircleResidual ⊆ {θ : ℝ | (1:ℝ)/8 ≤ |Real.sin θ|} := by
  apply Subset.trans _ circleStationaryResidual_support
  apply closure_mono
  intro x hx hh
  have he : compactCircleResidual x = 0 := by
    unfold compactCircleResidual
    by_cases hx' : x ∈ Ioo (-Real.pi) Real.pi <;> simp [hx',hh]
  exact hx he

 theorem circleResidualAmplitude_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (circleResidualAmplitude f) :=
  (Complex.ofRealCLM.contDiff.comp compactCircleResidual_contDiff).mul hf

 theorem circleResidualAmplitude_support (f : ℝ → ℂ) :
    tsupport (circleResidualAmplitude f) ⊆ tsupport compactCircleResidual := by
  apply closure_mono
  intro x hx hh
  exact hx (by simp [circleResidualAmplitude,hh])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_CompactMultiplierScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem compact_multiplier_uniform_derivatives {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport w ⊆ K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      ∀ {C D : ℝ}, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ∀ k ≤ n, ∀ x, ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ (A*C)*D^k := by
  choose A hA hbound using fun k => compact_weighted_composition_scale hw
    (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) hK k
  let B : ℝ := ∑ k ∈ Finset.range (n+1), A k
  refine ⟨B,Finset.sum_nonneg (fun k _ => hA k),?_⟩
  intro f hf C D hC hD hb k hk x
  have hkB : A k ≤ B := Finset.single_le_sum (fun l _ => hA l)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  by_cases hx : x ∈ K
  · have hh := hbound k f hf C D hC hD (fun l hl => hb l (hl.trans hk)) x hx
    change ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ A k*C*D^k at hh
    apply hh.trans
    gcongr
  · have he : iteratedDeriv k (fun y => w y*f y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (tsupport_mul_subset_left
        (complex_iteratedDeriv_tsupport _ k hh))))
    rw [he,norm_zero]
    have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => hA k)
    positivity

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleResidualDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem circle_residual_uniform_decay (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {C D Λ : ℝ}, 0 ≤ C → 1 ≤ D → 0 < Λ →
    (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖∫ x : ℝ, cosineOscillator Λ x * circleResidualAmplitude f x‖ ≤ A*C*D^n/Λ^n := by
  let w : ℝ → ℂ := fun x => (compactCircleResidual x : ℂ)
  have hw : ContDiff ℝ ∞ w := Complex.ofRealCLM.contDiff.comp compactCircleResidual_contDiff
  have hws : tsupport w ⊆ Icc (-Real.pi) Real.pi := by
    apply Subset.trans _ compactCircleResidual_tsupport
    apply closure_mono
    intro x hx hh
    exact hx (by simp [w,hh])
  obtain ⟨B,hB,hprod⟩ := compact_multiplier_uniform_derivatives hw isCompact_Icc hws n
  obtain ⟨A,hA,hbound⟩ := angular_nonstationary_uniform (by norm_num : (0:ℝ)<1/8)
    (neg_le_self Real.pi_pos.le) n
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro f hf C D Λ hC hD hΛ hb
  have hs : tsupport (circleResidualAmplitude f) ⊆ Icc (-Real.pi) Real.pi :=
    (circleResidualAmplitude_support f).trans compactCircleResidual_tsupport
  have haway : ∀ x ∈ tsupport (circleResidualAmplitude f), (1:ℝ)/8 ≤ |Real.sin x| :=
    fun x hx => compactCircleResidual_sine_support (circleResidualAmplitude_support f hx)
  have hder : ∀ k ≤ n, ∀ x, ‖iteratedDeriv k (circleResidualAmplitude f) x‖ ≤ (B*C)*D^k :=
    hprod hf hC hD hb
  have hh := hbound (circleResidualAmplitude_contDiff hf) hs haway (mul_nonneg hB hC) hD hΛ hder
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationaryCosineCutoff_periodic : Function.Periodic
    (fun θ => stationaryCutoff (stationaryCosineChart θ)) (2*Real.pi) := by
  intro θ
  have he : (θ+2*Real.pi)/2 = θ/2+Real.pi := by ring
  simp only [stationaryCosineChart,he,Real.cos_add_pi,mul_neg]
  exact stationaryCutoff.neg _

 theorem cosineOscillator_periodic (Λ : ℝ) : Function.Periodic (cosineOscillator Λ) (2*Real.pi) := by
  intro θ
  simp [cosineOscillator,Real.cos_add_two_pi]

 theorem stationaryCosineCutoff_add_pi (θ : ℝ) :
    stationaryCutoff (stationaryCosineChart (θ+Real.pi)) = stationaryCutoff (stationarySineChart θ) := by
  have he : (θ+Real.pi)/2 = θ/2+Real.pi/2 := by ring
  simp only [stationaryCosineChart,he,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
    mul_zero,mul_one,zero_sub,mul_neg,stationarySineChart]
  exact stationaryCutoff.neg _

 theorem cosineOscillator_add_pi (Λ θ : ℝ) :
    cosineOscillator Λ (θ+Real.pi) = cosineOscillator (-Λ) θ := by
  simp only [cosineOscillator,Real.cos_add_pi,Complex.ofReal_neg]
  congr 1
  ring

 theorem circle_negative_piece (Λ : ℝ) {f : ℝ → ℂ}
    (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
      (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ) =
      localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) := by
  let G : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ
  have hG : Function.Periodic G (2*Real.pi) := by
    intro θ
    simp only [G,cosineOscillator_periodic Λ θ,stationaryCosineCutoff_periodic θ,hp θ]
  have hs := hG.intervalIntegral_add_eq (-Real.pi) 0
  have he₁ : -Real.pi+2*Real.pi = Real.pi := by ring
  simp only [he₁,zero_add] at hs
  change (∫ θ in (-Real.pi)..Real.pi, G θ) = _
  rw [hs]
  have he₂ : (∫ θ in (-Real.pi)..Real.pi, G (θ+Real.pi)) = ∫ θ in (0:ℝ)..2*Real.pi, G θ := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  rw [← he₂]
  have hGF : (fun θ => G (θ+Real.pi)) = fun θ => cosineOscillator (-Λ) θ *
      (stationaryCutoff (stationarySineChart θ):ℂ)*f (θ+Real.pi) := by
    funext θ
    simp only [G,cosineOscillator_add_pi,stationaryCosineCutoff_add_pi]
  rw [hGF]
  exact circlePositivePiece_localized (-Λ) _

 theorem circle_residual_integral (Λ : ℝ) (f : ℝ → ℂ) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ *
      (circleStationaryResidual θ:ℂ)*f θ) =
    ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ := by
  let F : ℝ → ℂ := fun θ => cosineOscillator Λ θ * (circleStationaryResidual θ:ℂ)*f θ
  have hπ : circleStationaryResidual Real.pi = 0 := by
    apply circleStationaryResidual_zero_cosine
    simp [stationaryCosineChart]
  have he : (fun θ => cosineOscillator Λ θ * circleResidualAmplitude f θ) =
      (Ioc (-Real.pi) Real.pi).indicator F := by
    funext θ
    by_cases ht : θ ∈ Ioo (-Real.pi) Real.pi
    · have ht' : θ ∈ Ioc (-Real.pi) Real.pi := ⟨ht.1,ht.2.le⟩
      simp only [circleResidualAmplitude,compactCircleResidual,indicator_of_mem ht,
        indicator_of_mem ht',F]
      ring
    · by_cases ht' : θ ∈ Ioc (-Real.pi) Real.pi
      · have he : θ = Real.pi := by
          simp only [mem_Ioo,not_and_or,not_lt] at ht
          rcases ht with ht | ht <;> linarith [ht'.1,ht'.2]
        subst θ
        simp [circleResidualAmplitude,compactCircleResidual,F,hπ,ht']
      · simp [circleResidualAmplitude,compactCircleResidual,ht,ht']
  rw [he,integral_indicator measurableSet_Ioc]
  exact intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)

 theorem full_circle_decomposition (Λ : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hp : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ * f θ) =
      localizedCircleIntegral Λ f + localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) +
        ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ := by
  let F₀ : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationarySineChart θ):ℂ)*f θ
  let Fπ : ℝ → ℂ := fun θ => cosineOscillator Λ θ *
    (stationaryCutoff (stationaryCosineChart θ):ℂ)*f θ
  let Fr : ℝ → ℂ := fun θ => cosineOscillator Λ θ * (circleStationaryResidual θ:ℂ)*f θ
  have hE := cosineOscillator_continuous Λ
  have hcs : Continuous stationarySineChart := by unfold stationarySineChart; fun_prop
  have hcc : Continuous stationaryCosineChart := by unfold stationaryCosineChart; fun_prop
  have h₀ : Continuous F₀ := (hE.mul (Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hcs))).mul hf
  have hπ : Continuous Fπ := (hE.mul (Complex.continuous_ofReal.comp (stationaryCutoff.continuous.comp hcc))).mul hf
  have hr : Continuous Fr := (hE.mul (Complex.continuous_ofReal.comp circleStationaryResidual_contDiff.continuous)).mul hf
  have he : (fun θ => cosineOscillator Λ θ*f θ) = fun θ => (F₀ θ+Fπ θ)+Fr θ := by
    funext θ
    dsimp [F₀,Fπ,Fr,circleStationaryResidual]
    push_cast
    ring
  have hi₁ := intervalIntegral.integral_add (μ := volume) ((h₀.add hπ).intervalIntegrable (-Real.pi) Real.pi)
    (hr.intervalIntegrable (-Real.pi) Real.pi)
  have hi₀ := intervalIntegral.integral_add (μ := volume) (h₀.intervalIntegrable (-Real.pi) Real.pi)
    (hπ.intervalIntegrable (-Real.pi) Real.pi)
  simp only [Pi.add_apply] at hi₁
  rw [he,hi₁,hi₀]

  rw [show (∫ θ in (-Real.pi)..Real.pi, F₀ θ) = localizedCircleIntegral Λ f from
    circlePositivePiece_localized Λ f,
    show (∫ θ in (-Real.pi)..Real.pi, Fπ θ) = localizedCircleIntegral (-Λ) (fun θ => f (θ+Real.pi)) from
    circle_negative_piece Λ hp,
    show (∫ θ in (-Real.pi)..Real.pi, Fr θ) = ∫ θ : ℝ, cosineOscillator Λ θ * circleResidualAmplitude f θ from
    circle_residual_integral Λ f]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem full_circle_stationary_expansion_oai (n M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    Function.Periodic f (2*Real.pi) → ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ max (2*(n+1)+2) M, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f θ) - fullCircleStationaryExpansion Λ f n‖ ≤
      ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (A*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M := by
  obtain ⟨A₀,hA₀,h₀⟩ := localized_stationary_uniform_remainder n
  obtain ⟨Aπ,hAπ,hπ⟩ := localized_stationary_opposite_remainder n
  obtain ⟨B,hB,hr⟩ := circle_residual_uniform_decay M
  refine ⟨A₀+Aπ,B,add_nonneg hA₀ hAπ,hB,?_⟩
  intro f hf hp Λ C D hΛ hC hD hb
  have hbf : ∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k :=
    fun k hk => hb k (hk.trans (le_max_left _ _))
  have hbs : ∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k (fun θ => f (θ+Real.pi)) x‖ ≤ C*D^k := by
    intro k hk x
    rw [iteratedDeriv_comp_add_const]
    exact hbf k hk _
  have hfs : ContDiff ℝ ∞ (fun θ => f (θ+Real.pi)) := hf.comp (contDiff_id.add contDiff_const)
  have hh₀ := h₀ hf hΛ hC hD hbf
  have hhπ := hπ hfs hΛ hC hD hbs
  have hhr := hr hf hC hD hΛ (fun k hk => hb k (hk.trans (le_max_right _ _)))
  rw [full_circle_decomposition Λ hf.continuous hp]
  unfold fullCircleStationaryExpansion
  have he (a b r x y : ℂ) : a+b+r-(x+y) = ((a-x)+(b-y))+r := by ring
  rw [he]
  have hn (a b r : ℂ) : ‖a+b+r‖ ≤ ‖a‖+‖b‖+‖r‖ :=
    (norm_add_le (a+b) r).trans (add_le_add (norm_add_le a b) (le_refl ‖r‖))
  apply (hn _ _ _).trans
  calc
    _ ≤ ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (A₀*C*D^(2*(n+1)+2)) +
        ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (Aπ*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M := add_le_add (add_le_add hh₀ hhπ) hhr
    _ = _ := by ring

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.full_circle_stationary_expansion_oai := @OAI.PlanarFalconer.full_circle_stationary_expansion_oai
