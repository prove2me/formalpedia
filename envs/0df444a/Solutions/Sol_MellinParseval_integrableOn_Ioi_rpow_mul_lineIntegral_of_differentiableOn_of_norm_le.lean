-- Prove2me | solution 1 for MellinParseval.integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b40f1286-030d-5fd7-8f4d-263a9f651d56

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le

set_option autoImplicit false

section

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace MellinParseval

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

private theorem integral_sesq_fourier_fourier (M : E →L⋆[ℂ] F →L[ℂ] G) {a : ℝ → E} {b : ℝ → F}
    (ha : Integrable a) (hb : Integrable b) (hb' : Integrable (𝓕 b)) (hbc : Continuous b) :
    ∫ ξ : ℝ, M (𝓕 a ξ) (𝓕 b ξ) = ∫ t : ℝ, M (a t) (b t) := by
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (L := innerₗ ℝ) M
    continuous_fourierChar continuous_inner ha hb'
  rw [flip_innerₗ] at h
  have h' : ∫ ξ : ℝ, M (𝓕 a ξ) (𝓕 b ξ) = ∫ x : ℝ, M (a x) (𝓕⁻ (𝓕 b) x) := h
  rw [hbc.fourierInv_fourier_eq hb hb'] at h'
  exact h'

private theorem integral_sesq_fourierInv_fourierInv (M : E →L⋆[ℂ] F →L[ℂ] G) {a : ℝ → E} {b : ℝ → F}
    (ha : Integrable a) (hb : Integrable b) (hb' : Integrable (𝓕⁻ b)) (hbc : Continuous b) :
    ∫ ξ : ℝ, M (𝓕⁻ a ξ) (𝓕⁻ b ξ) = ∫ t : ℝ, M (a t) (b t) := by
  rw [fourierInv_eq_fourier_comp_neg a, fourierInv_eq_fourier_comp_neg b]
  have hb'' : Integrable (𝓕 fun x : ℝ => b (-x)) := by
    rw [← fourierInv_eq_fourier_comp_neg b]
    exact hb'
  rw [integral_sesq_fourier_fourier M ha.comp_neg hb.comp_neg hb'' (hbc.comp continuous_neg)]
  exact integral_neg_eq_self (fun t : ℝ => M (a t) (b t)) volume

private def lineProfile (σ : ℝ) (a : ℝ → E) (y : ℝ) : E :=
  ∫ t : ℝ, (((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) • a t)

private def HasIntegrableProfile (σ : ℝ) (b : ℝ → F) : Prop :=
  IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) • lineProfile σ b y) (Set.Ioi (0 : ℝ))

private def charIntegral (a : ℝ → E) (u : ℝ) : E :=
  ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) • a t

private theorem cpow_exp_eq (σ u t : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.exp (σ * u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_exp, mul_add, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1 <;> (congr 1; ring)

omit [CompleteSpace E] in

private theorem lineProfile_exp (σ : ℝ) (a : ℝ → E) (u : ℝ) :
    lineProfile σ a (Real.exp u) = ((Real.exp (σ * u) : ℝ) : ℂ) • charIntegral a u := by
  unfold lineProfile charIntegral
  rw [← integral_smul]
  congr 1
  funext t
  rw [cpow_exp_eq, mul_smul]

omit [CompleteSpace E] in

private theorem charIntegral_two_pi_mul (a : ℝ → E) (w : ℝ) : charIntegral a (2 * π * w) = 𝓕⁻ a w := by
  rw [fourierInv_eq']
  unfold charIntegral
  have h : ∀ t : ℝ, ((t * (2 * π * w) : ℝ) : ℂ) = ((2 * π * inner ℝ t w : ℝ) : ℂ) := fun t => by
    rw [Real.inner_apply]
    push_cast
    ring
  simp_rw [h]

omit [CompleteSpace F] in

private theorem HasIntegrableProfile.integrable_fourierInv {σ : ℝ} {b : ℝ → F}
    (hbp : HasIntegrableProfile σ b) : Integrable (𝓕⁻ b) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  have h1 := hbp
  unfold HasIntegrableProfile at h1
  rw [himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    integrableOn_univ] at h1
  have h2 : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-σ) / Real.exp u : ℝ) : ℂ)) •
      lineProfile σ b (Real.exp u)) = charIntegral b u := by
    intro u
    rw [lineProfile_exp, ← Complex.coe_smul, smul_smul, smul_smul]
    have hs : |Real.exp u| * (Real.exp u ^ (-σ) / Real.exp u) * Real.exp (σ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-σ) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    rw [hsC, one_smul]
  simp_rw [h2] at h1
  have h3 : Integrable (fun w : ℝ => charIntegral b (2 * π * w)) := h1.comp_mul_left' h2π
  simpa only [charIntegral_two_pi_mul] using h3

private theorem integral_sesq_lineProfile_lineProfile (M : E →L⋆[ℂ] F →L[ℂ] G) (σ₁ σ₂ : ℝ)
    {a : ℝ → E} {b : ℝ → F} (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b)
    (hbp : HasIntegrableProfile σ₂ b) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) • M (lineProfile σ₁ a y) (lineProfile σ₂ b y)
      = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b t) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  have hFb : Integrable (𝓕⁻ b) := hbp.integrable_fourierInv

  have hcollapse : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ)) •
      M (lineProfile σ₁ a (Real.exp u)) (lineProfile σ₂ b (Real.exp u)))
        = M (charIntegral a u) (charIntegral b u) := by
    intro u
    rw [lineProfile_exp, lineProfile_exp,
      map_smulₛₗ M ((Real.exp (σ₁ * u) : ℝ) : ℂ) (charIntegral a u), ContinuousLinearMap.smul_apply,
      map_smul (M (charIntegral a u)) ((Real.exp (σ₂ * u) : ℝ) : ℂ) (charIntegral b u),
      Complex.conj_ofReal, ← Complex.coe_smul, smul_smul, smul_smul, smul_smul]
    have hs : |Real.exp u| * (Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u) * Real.exp (σ₁ * u) *
        Real.exp (σ₂ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ₁ * u) : ℝ) : ℂ) * ((Real.exp (σ₂ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    rw [hsC, one_smul]
  calc ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) •
          M (lineProfile σ₁ a y) (lineProfile σ₂ b y)
      = ∫ u : ℝ, M (charIntegral a u) (charIntegral b u) := by
        rw [himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
          Measure.restrict_univ]
        exact integral_congr_ae (Filter.Eventually.of_forall hcollapse)
    _ = |2 * π| • ∫ w : ℝ, M (charIntegral a (2 * π * w)) (charIntegral b (2 * π * w)) := by
        rw [Measure.integral_comp_mul_left (fun u : ℝ => M (charIntegral a u) (charIntegral b u))
            (2 * π),
          smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h2π), one_smul]
    _ = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b t) := by
        simp_rw [charIntegral_two_pi_mul]
        rw [integral_sesq_fourierInv_fourierInv M ha hb hFb hbc, abs_of_pos (by positivity),
          Complex.coe_smul]

private theorem integral_sesq_lineProfile_lineProfile_neg (M : E →L⋆[ℂ] F →L[ℂ] G) (σ₁ σ₂ : ℝ)
    {a : ℝ → E} {b : ℝ → F} (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b)
    (hbp : HasIntegrableProfile σ₂ (fun t : ℝ => b (-t))) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) •
        M (lineProfile σ₁ a y) (lineProfile σ₂ (fun t : ℝ => b (-t)) y)
      = ((2 * π : ℝ) : ℂ) • ∫ t : ℝ, M (a t) (b (-t)) :=
  integral_sesq_lineProfile_lineProfile M σ₁ σ₂ ha hb.comp_neg (hbc.comp continuous_neg) hbp

private theorem integral_conj_lineProfile_mul_lineProfile (σ₁ σ₂ : ℝ) {a b : ℝ → ℂ}
    (ha : Integrable a) (hb : Integrable b) (hbc : Continuous b) (hbp : HasIntegrableProfile σ₂ b) :
    ∫ y in Set.Ioi (0 : ℝ), ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile σ₁ a y) * lineProfile σ₂ b y)
      = ((2 * π : ℝ) : ℂ) * ∫ t : ℝ, starRingEnd ℂ (a t) * b t := by
  have h := integral_sesq_lineProfile_lineProfile (innerSL ℂ : ℂ →L⋆[ℂ] ℂ →L[ℂ] ℂ) σ₁ σ₂ ha hb hbc hbp
  simpa only [innerSL_apply_apply, RCLike.inner_apply', smul_eq_mul] using h

private theorem integrableOn_conj_lineProfile_mul_lineProfile (σ₁ σ₂ : ℝ) {a b : ℝ → ℂ}
    (ha : Integrable a) (hbp : HasIntegrableProfile σ₂ b) :
    IntegrableOn (fun y : ℝ => ((y ^ (-(σ₁ + σ₂)) / y : ℝ) : ℂ) *
        (starRingEnd ℂ (lineProfile σ₁ a y) * lineProfile σ₂ b y)) (Set.Ioi 0) := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity
  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  rw [himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    integrableOn_univ]
  have h2 : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ)) *
      (starRingEnd ℂ (lineProfile σ₁ a (Real.exp u)) * lineProfile σ₂ b (Real.exp u)))
        = starRingEnd ℂ (charIntegral a u) * charIntegral b u := by
    intro u
    rw [lineProfile_exp, lineProfile_exp, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal,
      ← Complex.coe_smul, smul_eq_mul]
    have hs : |Real.exp u| * (Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u) * Real.exp (σ₁ * u) *
        Real.exp (σ₂ * u) = 1 := by
      rw [abs_of_pos (Real.exp_pos u), ← Real.exp_mul, div_eq_mul_inv, ← Real.exp_neg]
      simp only [← Real.exp_add]
      rw [← Real.exp_zero]
      congr 1
      ring
    have hsC : ((|Real.exp u| : ℝ) : ℂ) * ((Real.exp u ^ (-(σ₁ + σ₂)) / Real.exp u : ℝ) : ℂ) *
        ((Real.exp (σ₁ * u) : ℝ) : ℂ) * ((Real.exp (σ₂ * u) : ℝ) : ℂ) = 1 := by
      exact_mod_cast hs
    linear_combination (starRingEnd ℂ (charIntegral a u) * charIntegral b u) * hsC
  simp_rw [h2]
  refine (integrable_comp_mul_left_iff
    (fun u : ℝ => starRingEnd ℂ (charIntegral a u) * charIntegral b u) h2π).mp ?_
  simp only [charIntegral_two_pi_mul]
  have hFa : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) a) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner.neg) ha
  have hcont : Continuous (𝓕⁻ a) := hFa
  refine Integrable.bdd_mul (c := ∫ t : ℝ, ‖a t‖) hbp.integrable_fourierInv
    ((Complex.continuous_conj.comp hcont).aestronglyMeasurable) (Filter.Eventually.of_forall ?_)
  intro x
  rw [Complex.norm_conj]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (-innerₗ ℝ) a x

end MellinParseval

end

end

section

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace StripContour

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_cpow_smul {y : ℝ} (hy : 0 < y) (x t : ℝ) (v : E) :
    ‖((y : ℂ) ^ ((x : ℂ) + (t : ℂ) * Complex.I)) • v‖ = y ^ x * ‖v‖ := by
  have hre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hy, hre]

private theorem rpow_le_add_of_mem_uIcc {y : ℝ} (hy : 0 < y) {c d x : ℝ} (hx : x ∈ Set.uIcc c d) :
    y ^ x ≤ y ^ c + y ^ d := by
  have hc : 0 ≤ y ^ c := (Real.rpow_pos_of_pos hy c).le
  have hd : 0 ≤ y ^ d := (Real.rpow_pos_of_pos hy d).le
  rcases Set.mem_uIcc.1 hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rcases le_or_gt 1 y with hy1 | hy1
    · exact (Real.rpow_le_rpow_of_exponent_le hy1 h₂).trans (le_add_of_nonneg_left hc)
    · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1.le h₁).trans (le_add_of_nonneg_right hd)
  · rcases le_or_gt 1 y with hy1 | hy1
    · exact (Real.rpow_le_rpow_of_exponent_le hy1 h₂).trans (le_add_of_nonneg_right hd)
    · exact (Real.rpow_le_rpow_of_exponent_ge hy hy1.le h₁).trans (le_add_of_nonneg_left hc)

private theorem
rpow_le_add_of_mem_Icc {c d y : ℝ} (hc : 0 < c) (hy : y ∈ Set.Icc c d) (σ : ℝ) : y ^ σ ≤ c ^ σ + d ^ σ := by
  have hc' : 0 ≤ c ^ σ := (Real.rpow_pos_of_pos hc σ).le
  have hd' : 0 ≤ d ^ σ := (Real.rpow_pos_of_pos (hc.trans_le (hy.1.trans hy.2)) σ).le
  rcases le_or_gt 0 σ with hσ | hσ
  · exact (Real.rpow_le_rpow (hc.le.trans hy.1) hy.2 hσ).trans (le_add_of_nonneg_left hc')
  · exact (Real.rpow_le_rpow_of_nonpos hc hy.1 hσ.le).trans (le_add_of_nonneg_right hd')

private theorem abs_sub_lt_of_mem_uIcc {σ σ₀ σ₁ σ₂ x : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀)
    (hx : x ∈ Set.uIcc σ₁ σ₂) : |x - σ| < σ₀ := by
  rw [abs_sub_lt_iff] at h₁ h₂ ⊢
  rcases Set.mem_uIcc.1 hx with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

section Strip

variable {f : ℂ → E} {σ σ₀ : ℝ} {m : ℝ → ℝ}

private theorem continuous_line (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) :
    Continuous fun t : ℝ => f ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
  have hline : Continuous fun t : ℝ => (σ' : ℂ) + (t : ℂ) * Complex.I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine hf.continuousOn.comp_continuous hline fun t => ?_
  simpa using hσ'

private theorem integrable_kernel_line (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ => ((y : ℂ) ^ ((σ' : ℂ) + (t : ℂ) * Complex.I)) • f ((σ' : ℂ) + (t : ℂ) * Complex.I) := by
  refine (hm.const_mul (y ^ σ')).mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hk : Continuous fun t : ℝ => (y : ℂ) ^ ((σ' : ℂ) + (t : ℂ) * Complex.I) :=
      continuous_const.cpow (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        fun _ => Complex.ofReal_mem_slitPlane.2 hy
    exact (hk.smul (continuous_line hf hσ')).aestronglyMeasurable
  · rw [norm_cpow_smul hy]
    exact mul_le_mul_of_nonneg_left (hbound σ' hσ' t) (Real.rpow_pos_of_pos hy σ').le

private theorem
norm_horizontal_le (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) (c : ℝ) :
    ‖∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (c : ℂ) * Complex.I)) • f ((x : ℂ) + (c : ℂ) * Complex.I)‖
      ≤ (y ^ σ₁ + y ^ σ₂) * m c * |σ₂ - σ₁| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  have hx' : x ∈ Set.uIcc σ₁ σ₂ := Set.uIoc_subset_uIcc hx
  rw [norm_cpow_smul hy]
  exact mul_le_mul (rpow_le_add_of_mem_uIcc hy hx') (hbound x (abs_sub_lt_of_mem_uIcc h₁ h₂ hx') c)
    (norm_nonneg _) (by positivity)

private theorem norm_truncated_sub_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀})
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    ‖(∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I))
        - ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (y ^ σ₁ + y ^ σ₂) * (m a + m b) * |σ₂ - σ₁| := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hg : DifferentiableOn ℂ (fun s : ℂ => ((y : ℂ) ^ s) • f s) {s : ℂ | |s.re - σ| < σ₀} :=
    (differentiableOn_id.const_cpow (Or.inl hy0)).smul hf
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun s : ℂ => ((y : ℂ) ^ s) • f s)
    ⟨σ₁, a⟩ ⟨σ₂, b⟩ (hg.mono fun s hs => abs_sub_lt_of_mem_uIcc h₁ h₂ (Complex.mem_reProdIm.1 hs).1)
  dsimp only at hrect
  set Ha := ∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (a : ℂ) * Complex.I)) • f ((x : ℂ) + (a : ℂ) * Complex.I)
    with hHa
  set Hb := ∫ x : ℝ in σ₁..σ₂, ((y : ℂ) ^ ((x : ℂ) + (b : ℂ) * Complex.I)) • f ((x : ℂ) + (b : ℂ) * Complex.I)
    with hHb
  set V₂ := ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I)
    with hV₂
  set V₁ := ∫ t : ℝ in a..b, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    with hV₁
  have hV : Complex.I • (V₂ - V₁) = Hb - Ha := by
    rw [smul_sub, ← sub_eq_zero, ← hrect]
    abel
  have hnorm : ‖V₂ - V₁‖ = ‖Hb - Ha‖ := by
    rw [← hV, norm_smul, Complex.norm_I, one_mul]
  rw [hnorm]
  calc ‖Hb - Ha‖ ≤ ‖Hb‖ + ‖Ha‖ := norm_sub_le _ _
    _ ≤ (y ^ σ₁ + y ^ σ₂) * m b * |σ₂ - σ₁| + (y ^ σ₁ + y ^ σ₂) * m a * |σ₂ - σ₁| :=
        add_le_add (norm_horizontal_le hbound h₁ h₂ hy b) (norm_horizontal_le hbound h₁ h₂ hy a)
    _ = (y ^ σ₁ + y ^ σ₂) * (m a + m b) * |σ₂ - σ₁| := by ring

private theorem exists_le_and_norm_lt {M : ℝ → ℝ} (hM : Integrable M) (T₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, T₀ ≤ T ∧ ‖M T‖ < ε := by
  by_contra hcon
  have hall : ∀ T : ℝ, T₀ ≤ T → ε ≤ ‖M T‖ := fun T hT => not_lt.1 fun h => hcon ⟨T, hT, h⟩
  have hsub : Set.Ici T₀ ⊆ {T : ℝ | ε ≤ ‖M T‖} := fun T hT => hall T hT
  have hfin := hM.measure_norm_ge_lt_top hε
  have hle := measure_mono (μ := (volume : Measure ℝ)) hsub
  rw [Real.volume_Ici] at hle
  exact lt_irrefl _ (lt_of_le_of_lt hle hfin)

private theorem lineProfile_eq_of_abs_sub_lt (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {σ₁ σ₂ : ℝ} (h₁ : |σ₁ - σ| < σ₀) (h₂ : |σ₂ - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    MellinParseval.lineProfile σ₁ (fun t : ℝ => f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) y
      = MellinParseval.lineProfile σ₂ (fun t : ℝ => f ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) y := by
  unfold MellinParseval.lineProfile
  beta_reduce
  set L₁ := ∫ t : ℝ, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I) with hL₁
  set L₂ := ∫ t : ℝ, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I) with hL₂

  set D : ℝ → E := fun T =>
    (∫ t : ℝ in (-T)..T, ((y : ℂ) ^ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₂ : ℂ) + (t : ℂ) * Complex.I))
      - ∫ t : ℝ in (-T)..T, ((y : ℂ) ^ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) • f ((σ₁ : ℂ) + (t : ℂ) * Complex.I)
    with hD
  have hconv : Tendsto D atTop (𝓝 (L₂ - L₁)) :=
    (intervalIntegral_tendsto_integral (integrable_kernel_line hf hm hbound h₂ hy) tendsto_neg_atTop_atBot
        tendsto_id).sub
      (intervalIntegral_tendsto_integral (integrable_kernel_line hf hm hbound h₁ hy) tendsto_neg_atTop_atBot
        tendsto_id)

  set M : ℝ → ℝ := fun T => (y ^ σ₁ + y ^ σ₂) * |σ₂ - σ₁| * (m (-T) + m T) with hM
  have hMint : Integrable M := (hm.comp_neg.add hm).const_mul _
  have hDle : ∀ T : ℝ, ‖D T‖ ≤ M T := fun T =>
    (norm_truncated_sub_le hf hbound h₁ h₂ hy (-T) T).trans_eq (by simp only [hM]; ring)

  rw [eq_comm, ← sub_eq_zero]
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hconv) (ε / 2) (by positivity))
  obtain ⟨T, hTT₀, hMT⟩ := exists_le_and_norm_lt hMint T₀ (show (0 : ℝ) < ε / 2 by positivity)
  have hdist : ‖L₂ - L₁ - D T‖ < ε / 2 := by
    have := hT₀ T hTT₀
    rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
  have htri : ‖L₂ - L₁‖ ≤ ‖L₂ - L₁ - D T‖ + ‖D T‖ := by
    calc ‖L₂ - L₁‖ = ‖(L₂ - L₁ - D T) + D T‖ := by rw [sub_add_cancel]
      _ ≤ ‖L₂ - L₁ - D T‖ + ‖D T‖ := norm_add_le _ _
  have hMabs : M T ≤ ‖M T‖ := le_abs_self (M T)
  linarith [hDle T]

private theorem
lineProfile_eq_lineProfile_of_mem_Ioo (hσ₀ : 0 < σ₀) (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀})
    (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    {y : ℝ} (hy : 0 < y) {σ' : ℝ} (hσ' : σ' ∈ Set.Ioo (σ - σ₀) (σ + σ₀)) :
    MellinParseval.lineProfile σ' (fun t : ℝ => f ((σ' : ℂ) + (t : ℂ) * Complex.I)) y
      = MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y := by
  have h' : |σ' - σ| < σ₀ := by
    rw [abs_sub_lt_iff]
    exact ⟨by linarith [hσ'.2], by linarith [hσ'.1]⟩
  have h0 : |σ - σ| < σ₀ := by simpa using hσ₀
  exact lineProfile_eq_of_abs_sub_lt hf hm hbound h' h0 hy

private theorem norm_lineProfile_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    ‖MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖ ≤ y ^ σ' * ∫ t : ℝ, m t := by
  rw [lineProfile_eq_of_abs_sub_lt hf hm hbound hσσ hσ' hy]
  unfold MellinParseval.lineProfile
  beta_reduce
  refine (norm_integral_le_of_norm_le (hm.const_mul (y ^ σ')) (Eventually.of_forall fun t => ?_)).trans_eq
    (integral_const_mul _ _)
  rw [norm_cpow_smul hy]
  exact mul_le_mul_of_nonneg_left (hbound σ' hσ' t) (Real.rpow_pos_of_pos hy σ').le

private theorem continuousOn_lineProfile (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) :
    ContinuousOn (fun y : ℝ => MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y)
      (Set.Ioi 0) := by
  unfold MellinParseval.lineProfile
  beta_reduce
  have hIcc : ∀ c d : ℝ, 0 < c → c ≤ d →
      ContinuousOn (fun y : ℝ => ∫ t : ℝ, ((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) •
        f ((σ : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc c d) := by
    intro c d hc hcd
    refine continuousOn_of_dominated (bound := fun t => (c ^ σ + d ^ σ) * m t) ?_ ?_ (hm.const_mul _) ?_
    · intro y hy
      exact (integrable_kernel_line hf hm hbound hσσ (hc.trans_le hy.1)).aestronglyMeasurable
    · intro y hy
      refine Eventually.of_forall fun t => ?_
      rw [norm_cpow_smul (hc.trans_le hy.1)]
      exact mul_le_mul (rpow_le_add_of_mem_Icc hc hy σ) (hbound σ hσσ t) (norm_nonneg _)
        (add_nonneg (Real.rpow_pos_of_pos hc σ).le (Real.rpow_pos_of_pos (hc.trans_le hcd) σ).le)
    · refine Eventually.of_forall fun t => ?_
      exact (Complex.continuous_ofReal.continuousOn.cpow continuousOn_const fun y hy =>
        Complex.ofReal_mem_slitPlane.2 (hc.trans_le hy.1)).smul continuousOn_const
  intro y hy
  have hy' : (0 : ℝ) < y := hy
  exact ((hIcc (y / 2) (2 * y) (by positivity) (by linarith)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))).continuousWithinAt

private theorem rpow_neg_div_mul_rpow {y : ℝ} (hy : 0 < y) (σ σ' : ℝ) : y ^ (-σ) / y * y ^ σ' = y ^ (σ' - σ - 1) := by
  rw [Real.rpow_sub_one hy.ne', Real.rpow_sub hy, Real.rpow_neg hy.le]
  ring

private theorem norm_smul_lineProfile_le (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t)
    (hσσ : |σ - σ| < σ₀) {σ' : ℝ} (hσ' : |σ' - σ| < σ₀) {y : ℝ} (hy : 0 < y) :
    ‖((y ^ (-σ) / y : ℝ) : ℂ) •
        MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖
      ≤ (∫ t : ℝ, m t) * y ^ (σ' - σ - 1) := by
  have hr : 0 < y ^ (-σ) / y := by positivity
  rw [norm_smul, Complex.norm_of_nonneg hr.le]
  calc y ^ (-σ) / y * ‖MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y‖
      ≤ y ^ (-σ) / y * (y ^ σ' * ∫ t : ℝ, m t) :=
        mul_le_mul_of_nonneg_left (norm_lineProfile_le hf hm hbound hσσ hσ' hy) hr.le
    _ = (∫ t : ℝ, m t) * y ^ (σ' - σ - 1) := by rw [← rpow_neg_div_mul_rpow hy σ σ']; ring

private theorem hasIntegrableProfile_of_differentiableOn (hσ₀ : 0 < σ₀)
    (hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (hm : Integrable m)
    (hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t) :
    MellinParseval.HasIntegrableProfile σ fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hσσ : |σ - σ| < σ₀ := by simpa using hσ₀
  have hσp : |σ + σ₀ / 2 - σ| < σ₀ := by
    rw [abs_sub_lt_iff]; constructor <;> linarith
  have hσm : |σ - σ₀ / 2 - σ| < σ₀ := by
    rw [abs_sub_lt_iff]; constructor <;> linarith
  have hcont := continuousOn_lineProfile hf hm hbound hσσ

  have hmeas : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioi 0 →
      AEStronglyMeasurable (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) •
        MellinParseval.lineProfile σ (fun t : ℝ => f ((σ : ℂ) + (t : ℂ) * Complex.I)) y) (volume.restrict s) := by
    intro s hs hs0
    refine AEStronglyMeasurable.smul ?_ ((hcont.mono hs0).aestronglyMeasurable hs)
    exact (Complex.measurable_ofReal.comp ((measurable_id.pow_const (-σ)).div measurable_id)).aestronglyMeasurable
  unfold MellinParseval.HasIntegrableProfile
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  ·
    have hint : IntegrableOn (fun y : ℝ => (∫ t : ℝ, m t) * y ^ (σ + σ₀ / 2 - σ - 1)) (Set.Ioc (0 : ℝ) 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine hint.mono' (hmeas _ measurableSet_Ioc Set.Ioc_subset_Ioi_self) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => norm_smul_lineProfile_le hf hm hbound hσσ hσp hy.1
  ·
    have hint : IntegrableOn (fun y : ℝ => (∫ t : ℝ, m t) * y ^ (σ - σ₀ / 2 - σ - 1)) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hint.mono' (hmeas _ measurableSet_Ioi fun y hy => Set.mem_Ioi.2 (zero_lt_one.trans (Set.mem_Ioi.1 hy))) ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy =>
      norm_smul_lineProfile_le hf hm hbound hσσ hσm (zero_lt_one.trans (Set.mem_Ioi.1 hy))

end Strip

end StripContour

open MeasureTheory

theorem solution
    (σ σ₀ : ℝ) (_hσ₀ : 0 < σ₀) (f : ℂ → ℂ) (m : ℝ → ℝ)
    (_hf : DifferentiableOn ℂ f {s : ℂ | |s.re - σ| < σ₀}) (_hm : Integrable m)
    (_hbound : ∀ σ' : ℝ, |σ' - σ| < σ₀ → ∀ t : ℝ, ‖f ((σ' : ℂ) + (t : ℂ) * Complex.I)‖ ≤ m t) :
    IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) * f ((σ : ℂ) + (t : ℂ) * Complex.I)) (Set.Ioi 0) := by
  have h := StripContour.hasIntegrableProfile_of_differentiableOn _hσ₀ _hf _hm _hbound
  unfold MellinParseval.HasIntegrableProfile MellinParseval.lineProfile at h
  simpa only [smul_eq_mul] using h

end
end
end S_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le
end P2MW
export P2MW.S_MellinParseval_integrableOn_Ioi_rpow_mul_lineIntegral_of_differentiableOn_of_norm_le (solution)
