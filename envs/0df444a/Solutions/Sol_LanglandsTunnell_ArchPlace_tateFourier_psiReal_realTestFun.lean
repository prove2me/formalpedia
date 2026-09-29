-- Prove2me | solution 1 for LanglandsTunnell.ArchPlace.tateFourier_psiReal_realTestFun
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6c2904b7-7d57-5bfa-89fc-a53bdf9dd15b

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_LanglandsTunnell_ArchEpsilon
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun

set_option autoImplicit false

open Real Complex Filter Function MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace GaussianHermiteFourier

private def tateGaussianℝ : ℝ → ℂ := fun t => (Real.exp (-(π * t ^ 2)) : ℂ)

private def tateGaussianℂRadial : ℝ → ℂ := fun r => (Real.exp (-(2 * π * r ^ 2)) : ℂ)

section Toolkit

private lemma tateGaussianℝ_apply_cexp (x : ℝ) :
    tateGaussianℝ x = Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) := by
  show (Real.exp (-(π * x ^ 2)) : ℂ) = _
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

private lemma tateGaussianℝ_eq_cexp_fun :
    tateGaussianℝ = fun x : ℝ => Complex.exp (-(π : ℂ) * (x : ℂ) ^ 2) :=
  funext tateGaussianℝ_apply_cexp

private lemma pi_complex_re_pos : (0 : ℝ) < ((π : ℂ)).re := by
  simpa using Real.pi_pos

private lemma integrable_tateGaussianℝ : Integrable tateGaussianℝ := by
  rw [tateGaussianℝ_eq_cexp_fun]
  exact integrable_cexp_neg_mul_sq pi_complex_re_pos

private lemma fourier_tateGaussianℝ_selfdual : 𝓕 tateGaussianℝ = tateGaussianℝ := by
  rw [tateGaussianℝ_eq_cexp_fun]
  have h := fourier_gaussian_pi (b := 1) (by norm_num)
  simpa using h

private lemma fourier_const_mul (r : ℂ) (f : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x : ℝ => r * f x) w = r * 𝓕 f w := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  congr 1
  funext v
  simp only [Circle.smul_def]
  ring

end Toolkit

section SgnComponent

private def tateSgnGaussianℝ : ℝ → ℂ := fun x => (x : ℂ) * tateGaussianℝ x

private theorem tateSgnGaussianℝ_apply (x : ℝ) : tateSgnGaussianℝ x = (x : ℂ) * tateGaussianℝ x := rfl

private lemma hasDerivAt_tateGaussianℝ (ξ : ℝ) :
    HasDerivAt tateGaussianℝ (-(2 * (π : ℂ)) * tateSgnGaussianℝ ξ) ξ := by
  have h1 : HasDerivAt (fun w : ℂ => -(π : ℂ) * w ^ 2) (-(π : ℂ) * (2 * (ξ : ℂ))) (ξ : ℂ) := by
    simpa using (hasDerivAt_pow 2 ((ξ : ℂ))).const_mul (-(π : ℂ))
  have h2 := (h1.cexp).comp_ofReal (z := ξ)
  rw [tateGaussianℝ_eq_cexp_fun, tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp]
  convert h2 using 1
  ring

private lemma deriv_tateGaussianℝ_eq :
    deriv tateGaussianℝ = fun x : ℝ => -(2 * (π : ℂ)) * tateSgnGaussianℝ x := by
  funext x
  exact (hasDerivAt_tateGaussianℝ x).deriv

private lemma differentiable_tateGaussianℝ : Differentiable ℝ tateGaussianℝ :=
  fun x => (hasDerivAt_tateGaussianℝ x).differentiableAt

private lemma integrable_tateSgnGaussianℝ : Integrable tateSgnGaussianℝ := by
  have h := integrable_mul_cexp_neg_mul_sq (b := (π : ℂ)) pi_complex_re_pos
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp]

private lemma integrable_deriv_tateGaussianℝ : Integrable (deriv tateGaussianℝ) := by
  rw [deriv_tateGaussianℝ_eq]
  exact integrable_tateSgnGaussianℝ.const_mul _

private theorem fourier_tateSgnGaussianℝ :
    𝓕 tateSgnGaussianℝ = fun ξ : ℝ => -Complex.I * tateSgnGaussianℝ ξ := by
  have key := Real.fourier_deriv integrable_tateGaussianℝ differentiable_tateGaussianℝ
    integrable_deriv_tateGaussianℝ
  rw [deriv_tateGaussianℝ_eq, fourier_tateGaussianℝ_selfdual] at key
  have hL : 𝓕 (fun x : ℝ => -(2 * (π : ℂ)) * tateSgnGaussianℝ x)
      = fun ξ : ℝ => -(2 * (π : ℂ)) * 𝓕 tateSgnGaussianℝ ξ := by
    funext ξ
    exact fourier_const_mul _ _ ξ
  rw [hL] at key
  funext ξ
  have hξ := congrFun key ξ
  have h2π : (-(2 * (π : ℂ))) ≠ 0 := by
    simp [Real.pi_ne_zero]
  apply mul_left_cancel₀ h2π
  rw [hξ, smul_eq_mul, tateSgnGaussianℝ_apply]
  ring

end SgnComponent

section Definitions

private def hermiteGaussianℂ (a : ℕ) : ℂ → ℂ :=
  fun z => z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)

private theorem hermiteGaussianℂ_apply (a : ℕ) (z : ℂ) :
    hermiteGaussianℂ a z = z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := rfl

private def tateHermiteℂ (a : ℕ) : ℂ → ℂ := fun z => (π : ℂ)⁻¹ * z ^ a * tateGaussianℂRadial ‖z‖

private theorem tateHermiteℂ_apply (a : ℕ) (z : ℂ) :
    tateHermiteℂ a z = (π : ℂ)⁻¹ * z ^ a * tateGaussianℂRadial ‖z‖ := rfl

private def tateHermiteHatℂ (a : ℕ) : ℂ → ℂ :=
  fun z => (π : ℂ)⁻¹ * (-Complex.I * (starRingEnd ℂ) z) ^ a * tateGaussianℂRadial ‖z‖

private theorem tateHermiteHatℂ_apply (a : ℕ) (z : ℂ) :
    tateHermiteHatℂ a z
      = (π : ℂ)⁻¹ * (-Complex.I * (starRingEnd ℂ) z) ^ a * tateGaussianℂRadial ‖z‖ := rfl

private def tateFourierIntegralℂ (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ∫ z : ℂ, f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
    ∂((2 : ℝ≥0∞) • volume)

private theorem tateFourierIntegralℂ_def (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ f w
      = ∫ z : ℂ, f z
          * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
          ∂((2 : ℝ≥0∞) • volume) := rfl

end Definitions

section Toolkit

private lemma pi_pos' : (0 : ℝ) < π := Real.pi_pos

private lemma gaussian_norm_eq (z : ℂ) :
    ‖Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)‖ = Real.exp (-(2 * π) * ‖z‖ ^ 2) := by
  have h : (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) = ((-(2 * π) * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp, Complex.ofReal_re]

private lemma hermiteGaussianℂ_norm (a : ℕ) (z : ℂ) :
    ‖hermiteGaussianℂ a z‖ = ‖z‖ ^ a * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by
  rw [hermiteGaussianℂ_apply, norm_mul, norm_pow, gaussian_norm_eq]

private lemma tateHermiteℂ_eq_smul (a : ℕ) :
    tateHermiteℂ a = fun z => (π : ℂ)⁻¹ * hermiteGaussianℂ a z := by
  funext z
  rw [tateHermiteℂ_apply, hermiteGaussianℂ_apply]
  unfold tateGaussianℂRadial
  have h : ((Real.exp (-(2 * π * ‖z‖ ^ 2)) : ℝ) : ℂ)
      = Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h]
  ring

private lemma tateHermiteHatℂ_eq_smul (a : ℕ) (w : ℂ) :
    tateHermiteHatℂ a w
      = (π : ℂ)⁻¹ * ((-Complex.I * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2)) := by
  rw [tateHermiteHatℂ_apply]
  unfold tateGaussianℂRadial
  have h : ((Real.exp (-(2 * π * ‖w‖ ^ 2)) : ℝ) : ℂ)
      = Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h]
  ring

end Toolkit

section Integrability

private lemma integrable_rexp_neg_pi_norm_sq :
    Integrable (fun z : ℂ => Real.exp (-π * ‖z‖ ^ 2)) := by
  have h0 : Integrable (fun v : ℂ =>
      Complex.exp (-(π : ℂ) * (‖v‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), v⟫ : ℝ))) :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using pi_pos') 0 (0 : ℂ)
  have h1 := h0.norm
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  show ‖Complex.exp (-(π : ℂ) * (‖z‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), z⟫ : ℝ))‖
      = Real.exp (-π * ‖z‖ ^ 2)
  have h2 : (-(π : ℂ) * (‖z‖ : ℂ) ^ 2 + (0 : ℂ) * (⟪(0 : ℂ), z⟫ : ℝ))
      = ((-π * ‖z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, Complex.norm_exp, Complex.ofReal_re]

private lemma pow_mul_gaussian_le (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ k * Real.exp (-(2 * π) * r ^ 2)
      ≤ (1 + (k.factorial : ℝ) * (π⁻¹) ^ k) * Real.exp (-π * r ^ 2) := by
  have hπ : (0 : ℝ) < π := pi_pos'
  have hexp_pos : (0 : ℝ) < Real.exp (-(2 * π) * r ^ 2) := Real.exp_pos _
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k

  have h1 : r ^ k ≤ 1 + r ^ (2 * k) := by
    rcases le_total r 1 with h | h
    · have : r ^ k ≤ 1 := pow_le_one₀ hr h
      nlinarith [pow_nonneg hr (2 * k)]
    · have : r ^ k ≤ r ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      nlinarith

  have h2 : r ^ (2 * k) ≤ (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2) := by
    have hx : (0 : ℝ) ≤ π * r ^ 2 := by positivity
    have hb := Real.pow_div_factorial_le_exp (x := π * r ^ 2) hx k
    have hb' : (π * r ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (π * r ^ 2) := by
      rw [div_le_iff₀ hfac_pos] at hb
      linarith
    have hexpand : (π * r ^ 2) ^ k = π ^ k * r ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    rw [hexpand] at hb'
    have hπk : (0 : ℝ) < π ^ k := pow_pos hπ k
    calc r ^ (2 * k) = (π ^ k * r ^ (2 * k)) / π ^ k := by field_simp
      _ ≤ ((k.factorial : ℝ) * Real.exp (π * r ^ 2)) / π ^ k := by gcongr
      _ = (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2) := by
          rw [inv_pow]
          ring

  have hsplit : Real.exp (π * r ^ 2) * Real.exp (-(2 * π) * r ^ 2)
      = Real.exp (-π * r ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmono : Real.exp (-(2 * π) * r ^ 2) ≤ Real.exp (-π * r ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg r]
  calc r ^ k * Real.exp (-(2 * π) * r ^ 2)
      ≤ (1 + r ^ (2 * k)) * Real.exp (-(2 * π) * r ^ 2) := by
        apply mul_le_mul_of_nonneg_right h1 hexp_pos.le
    _ = Real.exp (-(2 * π) * r ^ 2) + r ^ (2 * k) * Real.exp (-(2 * π) * r ^ 2) := by ring
    _ ≤ Real.exp (-π * r ^ 2)
          + ((k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (π * r ^ 2))
            * Real.exp (-(2 * π) * r ^ 2) := by
        gcongr
    _ = Real.exp (-π * r ^ 2)
          + (k.factorial : ℝ) * (π⁻¹) ^ k
            * (Real.exp (π * r ^ 2) * Real.exp (-(2 * π) * r ^ 2)) := by ring
    _ = Real.exp (-π * r ^ 2)
          + (k.factorial : ℝ) * (π⁻¹) ^ k * Real.exp (-π * r ^ 2) := by rw [hsplit]
    _ = (1 + (k.factorial : ℝ) * (π⁻¹) ^ k) * Real.exp (-π * r ^ 2) := by ring

private theorem integrable_norm_pow_mul_gaussianℂ (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
  have hcont : Continuous (fun z : ℂ => ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
    fun_prop
  refine Integrable.mono'
    ((integrable_rexp_neg_pi_norm_sq).const_mul (1 + (k.factorial : ℝ) * (π⁻¹) ^ k))
    hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  have hnonneg : (0 : ℝ) ≤ ‖z‖ ^ k * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  exact pow_mul_gaussian_le k (norm_nonneg z)

private theorem integrable_hermiteGaussianℂ (a : ℕ) : Integrable (hermiteGaussianℂ a) := by
  have hcont : Continuous (hermiteGaussianℂ a) := by
    unfold hermiteGaussianℂ
    fun_prop
  refine Integrable.mono' (integrable_norm_pow_mul_gaussianℂ a)
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [hermiteGaussianℂ_norm]

private theorem integrable_norm_mul_hermiteGaussianℂ (a : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ * ‖hermiteGaussianℂ a z‖) := by
  refine (integrable_norm_pow_mul_gaussianℂ (a + 1)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2) = ‖z‖ * ‖hermiteGaussianℂ a z‖
  rw [hermiteGaussianℂ_norm, pow_succ]
  ring

end Integrability

section Wirtinger

private lemma hasFDerivAt_coe_norm_sq (z : ℂ) :
    HasFDerivAt (fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (2 • (innerSL ℝ z))) z := by
  exact Complex.ofRealCLM.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt

private lemma hasFDerivAt_gaussian_factor (z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z))))) z := by
  have hfun : (fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      = fun w : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ ^ 2 : ℝ) : ℂ)) := by
    funext w
    congr 1
    push_cast
    ring
  have hinner : HasFDerivAt (fun w : ℂ => -(2 * (π : ℂ)) * ((‖w‖ ^ 2 : ℝ) : ℂ))
      ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))) z :=
    (hasFDerivAt_coe_norm_sq z).const_mul (-(2 * (π : ℂ)))
  have h := hinner.cexp
  rw [hfun]
  convert h using 2 <;> first | rfl | (simp only [Complex.ofReal_pow]; done) | (push_cast; ring_nf)

private lemma hasFDerivAt_hermiteGaussianℂ (a : ℕ) (z : ℂ) :
    HasFDerivAt (hermiteGaussianℂ a)
      ((z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))
        + (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
            • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))) z := by
  have hpow : HasFDerivAt (fun w : ℂ => w ^ a)
      (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ)) z :=
    (hasDerivAt_pow a z).complexToReal_fderiv
  exact hpow.mul (hasFDerivAt_gaussian_factor z)

private theorem differentiable_hermiteGaussianℂ (a : ℕ) : Differentiable ℝ (hermiteGaussianℂ a) :=
  fun z => (hasFDerivAt_hermiteGaussianℂ a z).differentiableAt

private lemma fderiv_hermiteGaussianℂ_apply_one (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) 1
      = (a : ℂ) * z ^ (a - 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        - (4 * (π : ℂ)) * (z.re : ℂ) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hinner1 : (innerSL ℝ z) (1 : ℂ) = z.re := by
    simp [innerSL_apply_apply, Complex.inner]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, hinner1, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

private lemma fderiv_hermiteGaussianℂ_apply_I (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I
      = (a : ℂ) * z ^ (a - 1) * Complex.I * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
        - (4 * (π : ℂ)) * (z.im : ℂ) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hinnerI : (innerSL ℝ z) Complex.I = z.im := by
    simp [innerSL_apply_apply, Complex.inner]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply, hinnerI, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  ring

private theorem wirtinger_hermiteGaussianℂ (a : ℕ) (z : ℂ) :
    (fderiv ℝ (hermiteGaussianℂ a) z) 1 + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)
      = -(4 * (π : ℂ)) * hermiteGaussianℂ (a + 1) z := by
  rw [fderiv_hermiteGaussianℂ_apply_one, fderiv_hermiteGaussianℂ_apply_I,
    hermiteGaussianℂ_apply]
  have hz : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    rw [mul_comm]
    exact Complex.re_add_im z
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc ((a : ℂ) * z ^ (a - 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          - (4 * (π : ℂ)) * (z.re : ℂ) * z ^ a
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
        + Complex.I * ((a : ℂ) * z ^ (a - 1) * Complex.I
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          - (4 * (π : ℂ)) * (z.im : ℂ) * z ^ a
              * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
      = (1 + Complex.I * Complex.I) * ((a : ℂ) * z ^ (a - 1)
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
        - (4 * (π : ℂ)) * ((z.re : ℂ) + Complex.I * (z.im : ℂ)) * z ^ a
            * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by ring
    _ = -(4 * (π : ℂ)) * (z * z ^ a * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
        rw [hI2, hz]
        ring
    _ = -(4 * (π : ℂ)) * (z ^ (a + 1) * Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
        rw [pow_succ]
        ring

private theorem integrable_fderiv_hermiteGaussianℂ (a : ℕ) :
    Integrable (fderiv ℝ (hermiteGaussianℂ a)) := by

  have hcd : ContDiff ℝ 1 (hermiteGaussianℂ a) := by
    unfold hermiteGaussianℂ
    have h1 : ContDiff ℝ 1 (fun z : ℂ => z ^ a) := contDiff_id.pow a
    have h2 : ContDiff ℝ 1 (fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)) := by
      have hbody : ContDiff ℝ 1 (fun z : ℂ => -(2 * (π : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
        have hns : ContDiff ℝ 1 (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) := contDiff_norm_sq ℝ
        exact (Complex.ofRealCLM.contDiff.comp hns).const_smul (-(2 * (π : ℂ)))
      have hbody' : (fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
          = fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
        funext w
        congr 1
        push_cast
        ring
      rw [hbody']
      exact hbody.cexp
    exact h1.mul h2
  have hmeas : AEStronglyMeasurable (fderiv ℝ (hermiteGaussianℂ a)) volume :=
    (hcd.continuous_fderiv one_ne_zero).aestronglyMeasurable

  have hdom : Integrable (fun z : ℂ =>
      (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))
        + 8 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))) := by
    exact ((integrable_norm_pow_mul_gaussianℂ (a - 1)).const_mul (a : ℝ)).add
      ((integrable_norm_pow_mul_gaussianℂ (a + 1)).const_mul (8 * π))
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun z => ?_)

  rw [(hasFDerivAt_hermiteGaussianℂ a z).fderiv]
  have hgauss_norm : ‖Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)‖
      = Real.exp (-(2 * π) * ‖z‖ ^ 2) := gaussian_norm_eq z
  have hexp_le_one' : Real.exp (-(2 * π) * ‖z‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg ‖z‖, pi_pos']
  have hb1 : ‖(z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
      • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))‖
      ≤ ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖))) := by
    rw [norm_smul, norm_smul, norm_smul]
    have hcomp : ‖Complex.ofRealCLM.comp (2 • (innerSL ℝ z))‖ ≤ 2 * ‖z‖ := by
      have h2eq : (2 • (innerSL ℝ z) : ℂ →L[ℝ] ℝ) = (2 : ℝ) • (innerSL ℝ z) := by
        module
      rw [h2eq]
      calc ‖Complex.ofRealCLM.comp ((2 : ℝ) • (innerSL ℝ z))‖
          ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖(2 : ℝ) • (innerSL ℝ z)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (2 * ‖z‖) := by
            apply mul_le_mul
            · exact Complex.ofRealCLM.opNorm_le_bound zero_le_one
                (fun x => by simp [Complex.ofRealCLM_apply])
            · rw [norm_smul]
              simp only [Real.norm_ofNat]
              have := innerSL_apply_norm (𝕜 := ℝ) z
              calc (2 : ℝ) * ‖innerSL ℝ z‖ = 2 * ‖z‖ := by rw [this]
                _ ≤ 2 * ‖z‖ := le_rfl
            · positivity
            · norm_num
        _ = 2 * ‖z‖ := by ring
    have hnegtwo : ‖(-(2 * (π : ℂ)))‖ = 2 * π := by
      rw [norm_neg]
      have : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [norm_pow, hgauss_norm, hnegtwo]
    have hz2 : (0 : ℝ) ≤ 2 * ‖z‖ := by positivity
    gcongr
  have hb2 : ‖(Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
      • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))‖
      ≤ Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) := by
    rw [norm_smul, norm_smul, hgauss_norm]
    have h1le : ‖(1 : ℂ →L[ℝ] ℂ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hca : ‖(a : ℂ) * z ^ (a - 1)‖ = (a : ℝ) * ‖z‖ ^ (a - 1) := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc Real.exp (-(2 * π) * ‖z‖ ^ 2) * (‖(a : ℂ) * z ^ (a - 1)‖ * ‖(1 : ℂ →L[ℝ] ℂ)‖)
        ≤ Real.exp (-(2 * π) * ‖z‖ ^ 2) * (‖(a : ℂ) * z ^ (a - 1)‖ * 1) := by
          gcongr
        _ = Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) := by
          rw [mul_one, hca]
  calc ‖(z ^ a) • (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2)
          • ((-(2 * (π : ℂ))) • (Complex.ofRealCLM.comp (2 • (innerSL ℝ z)))))
        + (Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2))
            • (((a : ℂ) * z ^ (a - 1)) • (1 : ℂ →L[ℝ] ℂ))‖
      ≤ ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖)))
        + Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1)) :=
        (norm_add_le _ _).trans (add_le_add hb1 hb2)
    _ ≤ (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2))
        + 8 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
        have h1 : ‖z‖ ^ a * (Real.exp (-(2 * π) * ‖z‖ ^ 2) * (2 * π * (2 * ‖z‖)))
            = 4 * π * (‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by
          rw [pow_succ]
          ring
        have h2 : Real.exp (-(2 * π) * ‖z‖ ^ 2) * ((a : ℝ) * ‖z‖ ^ (a - 1))
            = (a : ℝ) * (‖z‖ ^ (a - 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2)) := by ring
        rw [h1, h2]
        have hpos : (0 : ℝ) ≤ ‖z‖ ^ (a + 1) * Real.exp (-(2 * π) * ‖z‖ ^ 2) := by positivity
        nlinarith [pi_pos']

end Wirtinger

section CoreComputation

private lemma fourierℂ_const_mul (r : ℂ) (f : ℂ → ℂ) (ξ : ℂ) :
    𝓕 (fun z : ℂ => r * f z) ξ = r * 𝓕 f ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← MeasureTheory.integral_const_mul]
  congr 1
  funext v
  simp only [Circle.smul_def]
  ring

private lemma fourierℂ_gaussian_base (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ 0) ξ
      = (2 : ℂ)⁻¹ * Complex.exp (-((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2) := by
  have h2π : (0 : ℝ) < (2 * (π : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simpa using pi_pos'
  have hfun : hermiteGaussianℂ 0 = fun z : ℂ => Complex.exp (-(2 * (π : ℂ)) * ((‖z‖ : ℂ)) ^ 2) := by
    funext z
    rw [hermiteGaussianℂ_apply, pow_zero, one_mul]
  have hmain := fourier_gaussian_innerProductSpace (V := ℂ) (b := 2 * (π : ℂ)) h2π ξ
  rw [hfun]
  have hdim : (Module.finrank ℝ ℂ : ℂ) / 2 = 1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  rw [hmain]
  have hexp : -(π : ℂ) ^ 2 * ((‖ξ‖ : ℂ)) ^ 2 / (2 * (π : ℂ)) = -((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2 := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hcoef : ((π : ℂ) / (2 * (π : ℂ))) ^ ((Module.finrank ℝ ℂ : ℂ) / 2) = (2 : ℂ)⁻¹ := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase : (π : ℂ) / (2 * (π : ℂ)) = (2 : ℂ)⁻¹ := by
      field_simp
    rw [hbase, hdim, Complex.cpow_one]
  rw [hcoef, hexp]

private lemma fourierℂ_hermite_succ (a : ℕ) (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ (a + 1)) ξ = (-Complex.I / 2) * ξ * 𝓕 (hermiteGaussianℂ a) ξ := by

  have hkey := Real.fourier_fderiv (V := ℂ) (integrable_hermiteGaussianℂ a)
    (differentiable_hermiteGaussianℂ a) (integrable_fderiv_hermiteGaussianℂ a)

  have happly : ∀ y : ℂ, 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) y) ξ
      = (2 * (π : ℂ) * Complex.I * (⟪ξ, y⟫ : ℝ)) * 𝓕 (hermiteGaussianℂ a) ξ := by
    intro y
    have h1 : 𝓕 (fderiv ℝ (hermiteGaussianℂ a)) ξ y
        = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) y) ξ :=
      Real.fourier_continuousLinearMap_apply (integrable_fderiv_hermiteGaussianℂ a)
    have h2 : 𝓕 (fderiv ℝ (hermiteGaussianℂ a)) ξ y
        = -(2 * (π : ℂ) * Complex.I) * ((-(⟪ξ, y⟫ : ℝ)) • 𝓕 (hermiteGaussianℂ a) ξ) := by
      rw [hkey]
      rfl
    rw [← h1, h2, Complex.real_smul]
    push_cast
    ring

  have hinner1 : (⟪ξ, (1 : ℂ)⟫ : ℝ) = ξ.re := by
    simp [Complex.inner]
  have hinnerI : (⟪ξ, Complex.I⟫ : ℝ) = ξ.im := by
    simp [Complex.inner]

  have hint1 : Integrable (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) :=
    (integrable_fderiv_hermiteGaussianℂ a).apply_continuousLinearMap 1
  have hintI : Integrable (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) :=
    (integrable_fderiv_hermiteGaussianℂ a).apply_continuousLinearMap Complex.I

  have hcombine : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
        + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
      = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
        + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ := by
    have hsum : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
        = ∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) := by
      rw [Real.fourier_eq]
      congr 1
    have hsplit : ∀ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))
        = (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)
          + Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) := by
      intro v
      ring
    have hint1' : Integrable (fun v : ℂ =>
        (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)) := by
      have := (Real.fourierIntegral_convergent_iff (f := fun z : ℂ =>
        (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ).mpr hint1
      refine this.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def]
      ring
    have hintI' : Integrable (fun v : ℂ =>
        Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))) := by
      have := (Real.fourierIntegral_convergent_iff (f := fun z : ℂ =>
        (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ).mpr hintI
      have h2 := this.const_mul Complex.I
      refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Circle.smul_def]
      ring
    rw [hsum]
    calc ∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))
        = ∫ v : ℂ, ((𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1)
            + Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ)
              * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I))) := by
          congr 1
          funext v
          exact hsplit v
      _ = (∫ v : ℂ, (𝐞 (-⟪v, ξ⟫) : ℂ) * ((fderiv ℝ (hermiteGaussianℂ a) v) 1))
            + ∫ v : ℂ, Complex.I * ((𝐞 (-⟪v, ξ⟫) : ℂ)
              * ((fderiv ℝ (hermiteGaussianℂ a) v) Complex.I)) :=
          integral_add hint1' hintI'
      _ = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
            + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ := by
          rw [Real.fourier_eq, MeasureTheory.integral_const_mul, Real.fourier_eq]
          congr 2

  have hwirt : 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
        + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ
      = -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ := by
    have hfun : (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
          + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I))
        = fun z : ℂ => -(4 * (π : ℂ)) * hermiteGaussianℂ (a + 1) z := by
      funext z
      exact wirtinger_hermiteGaussianℂ a z
    rw [hfun, fourierℂ_const_mul]

  have hξ : (ξ.re : ℂ) + Complex.I * (ξ.im : ℂ) = ξ := by
    rw [mul_comm]
    exact Complex.re_add_im ξ
  have hmain : -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
      = (2 * (π : ℂ) * Complex.I * ξ) * 𝓕 (hermiteGaussianℂ a) ξ := by
    calc -(4 * (π : ℂ)) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
        = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1
            + Complex.I * ((fderiv ℝ (hermiteGaussianℂ a) z) Complex.I)) ξ := hwirt.symm
      _ = 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) 1) ξ
            + Complex.I * 𝓕 (fun z : ℂ => (fderiv ℝ (hermiteGaussianℂ a) z) Complex.I) ξ :=
          hcombine
      _ = (2 * (π : ℂ) * Complex.I * (ξ.re : ℂ)) * 𝓕 (hermiteGaussianℂ a) ξ
            + Complex.I * ((2 * (π : ℂ) * Complex.I * (ξ.im : ℂ))
              * 𝓕 (hermiteGaussianℂ a) ξ) := by
          rw [happly 1, happly Complex.I, hinner1, hinnerI]
      _ = (2 * (π : ℂ) * Complex.I * ((ξ.re : ℂ) + Complex.I * (ξ.im : ℂ)))
            * 𝓕 (hermiteGaussianℂ a) ξ := by ring
      _ = (2 * (π : ℂ) * Complex.I * ξ) * 𝓕 (hermiteGaussianℂ a) ξ := by rw [hξ]
  have h4π : (-(4 * (π : ℂ))) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

  have hgoal : (-(4 * (π : ℂ))) * 𝓕 (hermiteGaussianℂ (a + 1)) ξ
      = (-(4 * (π : ℂ))) * ((-Complex.I / 2) * ξ * 𝓕 (hermiteGaussianℂ a) ξ) := by
    rw [hmain]
    ring
  exact mul_left_cancel₀ h4π hgoal

private theorem fourierℂ_pow_mul_gaussian (a : ℕ) (ξ : ℂ) :
    𝓕 (hermiteGaussianℂ a) ξ
      = (2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * ξ ^ a
          * Complex.exp (-((π : ℂ) / 2) * ((‖ξ‖ : ℂ)) ^ 2) := by
  induction a with
  | zero =>
      rw [fourierℂ_gaussian_base]
      simp
  | succ a ih =>
      rw [fourierℂ_hermite_succ a ξ, ih]
      rw [pow_succ, pow_succ]
      ring

end CoreComputation

section TateBridge

private lemma tate_kernel_eq (z w : ℂ) :
    Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
      = Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) := by
  congr 1
  have hadd : z * w + (starRingEnd ℂ) (z * w) = ((2 * (z * w).re : ℝ) : ℂ) := by
    rw [Complex.add_conj]
  have hinner : (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ) = 2 * (z * w).re := by
    rw [Complex.inner]
    have hconj : (2 : ℂ) * (starRingEnd ℂ) w * (starRingEnd ℂ) z
        = (starRingEnd ℂ) (z * w + z * w) := by
      simp only [map_add, map_mul]
      ring
    rw [hconj, Complex.conj_re, Complex.add_re]
    ring
  rw [hadd, hinner]
  push_cast
  ring

private theorem tateFourierIntegralℂ_eq_fourier (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ f w = 2 * 𝓕 f (2 * (starRingEnd ℂ) w) := by
  rw [tateFourierIntegralℂ_def, Real.fourier_eq']
  rw [MeasureTheory.integral_smul_measure]
  have hpt : ∀ z : ℂ,
      f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w)))
        = Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) • f z := by
    intro z
    rw [tate_kernel_eq z w, smul_eq_mul]
    ring
  have hint : (∫ z : ℂ,
      f z * Complex.exp (-(2 * (π : ℂ) * Complex.I) * (z * w + (starRingEnd ℂ) (z * w))))
      = ∫ z : ℂ, Complex.exp ((↑(-2 * π * (⟪z, 2 * (starRingEnd ℂ) w⟫ : ℝ)) * Complex.I)) • f z := by
    congr 1
    funext z
    exact hpt z
  rw [hint]
  simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]

private theorem tateFourierIntegralℂ_pow_mul_gaussian (a : ℕ) (w : ℂ) :
    tateFourierIntegralℂ (hermiteGaussianℂ a) w
      = (-Complex.I * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by
  rw [tateFourierIntegralℂ_eq_fourier, fourierℂ_pow_mul_gaussian]
  have hnorm : ((‖2 * (starRingEnd ℂ) w‖ : ℝ) : ℂ) ^ 2 = 4 * ((‖w‖ : ℂ)) ^ 2 := by
    have h2 : ‖(2 : ℂ) * (starRingEnd ℂ) w‖ = 2 * ‖w‖ := by
      rw [norm_mul, RCLike.norm_conj]
      simp
    rw [h2]
    push_cast
    ring
  rw [hnorm]
  have hexp : -((π : ℂ) / 2) * (4 * ((‖w‖ : ℂ)) ^ 2) = -(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2 := by
    ring
  rw [hexp]
  have hpow : ((2 : ℂ) * (starRingEnd ℂ) w) ^ a = 2 ^ a * ((starRingEnd ℂ) w) ^ a := by
    rw [mul_pow]
  have hcoef : (2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a)
      = (-Complex.I * (starRingEnd ℂ) w) ^ a := by
    rw [hpow]
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [div_pow, mul_pow]
    field_simp
  calc (2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2))
      = ((2 : ℂ) * ((2 : ℂ)⁻¹ * (-Complex.I / 2) ^ a * (2 * (starRingEnd ℂ) w) ^ a))
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by ring
    _ = (-Complex.I * (starRingEnd ℂ) w) ^ a
          * Complex.exp (-(2 * (π : ℂ)) * ((‖w‖ : ℂ)) ^ 2) := by rw [hcoef]

end TateBridge

private theorem tateFourierIntegralℂ_comp_conj (f : ℂ → ℂ) (w : ℂ) :
    tateFourierIntegralℂ (fun z => f ((starRingEnd ℂ) z)) w
      = tateFourierIntegralℂ f ((starRingEnd ℂ) w) := by
  rw [tateFourierIntegralℂ_eq_fourier, tateFourierIntegralℂ_eq_fourier]
  congr 1
  have hcomp : (fun z : ℂ => f ((starRingEnd ℂ) z)) = f ∘ ⇑Complex.conjLIE := by
    funext z
    simp [Complex.conjLIE_apply]
  rw [hcomp, Real.fourier_comp_linearIsometry]
  rw [Complex.conjLIE_apply, Complex.conj_conj]
  rw [show (2 : ℂ) * (starRingEnd ℂ) w = (starRingEnd ℂ) (w + w) by rw [map_add]; ring]
  rw [Complex.conj_conj]
  ring_nf

section ArchPlaceObjects

open LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

private theorem realTestFun_zero_eq : realTestFun 0 = tateGaussianℝ := by
  funext x
  rw [realTestFun_zero_apply, tateGaussianℝ_apply_cexp, neg_mul]

private theorem realTestFun_one_eq : realTestFun 1 = tateSgnGaussianℝ := by
  funext x
  have hv : ((1 : ZMod 2)).val = 1 := by decide
  unfold realTestFun
  rw [hv, pow_one, tateSgnGaussianℝ_apply, tateGaussianℝ_apply_cexp, neg_mul]

private theorem complexTestFun_neg_natCast (a : ℕ) : complexTestFun (-(a : ℤ)) = hermiteGaussianℂ a := by
  funext z
  rw [hermiteGaussianℂ_apply, neg_mul]
  unfold complexTestFun
  simp

private theorem complexTestFun_natCast (a : ℕ) :
    complexTestFun (a : ℤ) = fun z => hermiteGaussianℂ a ((starRingEnd ℂ) z) := by
  funext z
  rw [hermiteGaussianℂ_apply, neg_mul, RCLike.norm_conj]
  unfold complexTestFun
  simp

private theorem psiReal_eq_fourierChar_neg (x : ℝ) : psiReal x = (Real.fourierChar (-x) : ℂ) := by
  rw [psiReal_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

private theorem psiComplex_eq_fourierChar_neg (z : ℂ) :
    psiComplex z = (Real.fourierChar (-(2 * z.re)) : ℂ) := by
  simp only [psiComplex_apply, Complex.add_conj, Real.fourierChar_apply]
  push_cast
  ring_nf

private theorem tateFourier_psiReal_eq (f : ℝ → ℂ) (y : ℝ) : tateFourier psiReal volume f y = 𝓕 f y := by
  rw [Real.fourier_real_eq]
  unfold tateFourier
  congr 1
  funext x
  rw [Circle.smul_def, smul_eq_mul, psiReal_apply, Real.fourierChar_apply, mul_comm]
  congr 1
  push_cast
  ring_nf

private theorem tateFourier_psiComplex_eq (f : ℂ → ℂ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) f w = tateFourierIntegralℂ f w := by
  unfold tateFourier tateFourierIntegralℂ
  simp only [psiComplex_apply, neg_mul]

private theorem tateFourier_psiReal_realTestFun (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by
  rw [tateFourier_psiReal_eq]
  by_cases h : a = 0
  · subst h
    rw [realTestFun_zero_eq, fourier_tateGaussianℝ_selfdual, ZMod.val_zero, pow_zero, one_mul]
  · have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have h1 : a = 1 := (h01 a).resolve_left h
    subst h1
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [realTestFun_one_eq, fourier_tateSgnGaussianℝ, hv, pow_one]

private theorem tateFourier_psiComplex_complexTestFun (k : ℤ) (w : ℂ) :
    tateFourier psiComplex ((2 : ℝ≥0∞) • volume) (complexTestFun k) w
      = (-Complex.I) ^ k.natAbs * complexTestFun (-k) w := by
  rw [tateFourier_psiComplex_eq]
  obtain ⟨a, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [complexTestFun_natCast, tateFourierIntegralℂ_comp_conj, tateFourierIntegralℂ_pow_mul_gaussian,
      complexTestFun_neg_natCast, hermiteGaussianℂ_apply, Complex.conj_conj, RCLike.norm_conj, Int.natAbs_natCast,
      mul_pow]
    ring
  · rw [complexTestFun_neg_natCast, tateFourierIntegralℂ_pow_mul_gaussian, neg_neg, complexTestFun_natCast]
    dsimp only
    rw [hermiteGaussianℂ_apply, Int.natAbs_neg, Int.natAbs_natCast, RCLike.norm_conj, mul_pow]
    ring

private theorem tateFourier_eq_tateFourier_neg {K : Type*} [Field K] [MeasurableSpace K] (ψ ψ₀ : AddChar K ℂ)
    (hψ : ∀ t, ψ t = ψ₀ (-t)) (μ : Measure K) (f : K → ℂ) (y : K) :
    tateFourier ψ μ f y = tateFourier ψ₀ μ f (-y) := by
  unfold tateFourier
  simp only [hψ, mul_neg]

private theorem realTestFun_neg (a : ZMod 2) (x : ℝ) : realTestFun a (-x) = (-1) ^ a.val * realTestFun a x := by
  unfold realTestFun
  push_cast
  ring_nf

private theorem complexTestFun_neg (k : ℤ) (z : ℂ) :
    complexTestFun k (-z) = (-1) ^ k.natAbs * complexTestFun k z := by
  unfold complexTestFun
  rw [map_neg, norm_neg, neg_pow, neg_pow z, ← Int.toNat_add_toNat_neg_eq_natAbs k, pow_add]
  ring

private theorem tateFourier_realTestFun_eq_signEpsilon_mul (ψ : AddChar ℝ ℂ)
    (hψ : ∀ x : ℝ, ψ x = (Real.fourierChar x : ℂ)) (a : ZMod 2) :
    tateFourier ψ volume (realTestFun a) = fun y => signEpsilon a * realTestFun a y := by
  funext y
  have hrefl : ∀ t, ψ t = psiReal (-t) := fun t => by rw [hψ, psiReal_eq_fourierChar_neg, neg_neg]
  rw [tateFourier_eq_tateFourier_neg ψ psiReal hrefl, tateFourier_psiReal_realTestFun, realTestFun_neg, ← mul_assoc,
    ← mul_pow, neg_mul_neg, mul_one]
  by_cases h : a = 0
  · subst h
    rw [ZMod.val_zero, pow_zero, signEpsilon_zero]
  · have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    have h1 : a = 1 := (h01 a).resolve_left h
    subst h1
    have hv : ((1 : ZMod 2)).val = 1 := by decide
    rw [hv, pow_one, signEpsilon_one]

private theorem tateFourier_complexTestFun_eq_I_pow_natAbs_mul_neg (ψ : AddChar ℂ ℂ)
    (hψ : ∀ z : ℂ, ψ z = (Real.fourierChar (2 * z.re) : ℂ)) (k : ℤ) :
    tateFourier ψ ((2 : ℝ≥0∞) • volume) (complexTestFun k)
      = fun w => Complex.I ^ k.natAbs * complexTestFun (-k) w := by
  funext w
  have hrefl : ∀ t, ψ t = psiComplex (-t) := fun t => by
    rw [hψ, psiComplex_eq_fourierChar_neg, Complex.neg_re, mul_neg, neg_neg]
  rw [tateFourier_eq_tateFourier_neg ψ psiComplex hrefl, tateFourier_psiComplex_complexTestFun, complexTestFun_neg,
    Int.natAbs_neg, ← mul_assoc, ← mul_pow, neg_mul_neg, mul_one]

end ArchPlaceObjects

end GaussianHermiteFourier

open MeasureTheory LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace

theorem solution (a : ZMod 2) (y : ℝ) :
    tateFourier psiReal volume (realTestFun a) y = (-Complex.I) ^ a.val * realTestFun a y := by
  exact GaussianHermiteFourier.tateFourier_psiReal_realTestFun a y

end
end S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun
end P2MW
export P2MW.S_LanglandsTunnell_ArchPlace_tateFourier_psiReal_realTestFun (solution)
