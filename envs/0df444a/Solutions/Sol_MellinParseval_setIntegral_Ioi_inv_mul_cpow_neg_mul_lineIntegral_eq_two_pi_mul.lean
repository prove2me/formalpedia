-- Prove2me | solution 1 for MellinParseval.setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/24e384e4-dc9f-5fa3-b2c5-b70b5f7ee27e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul

set_option autoImplicit false

noncomputable section

open MeasureTheory Real
open scoped FourierTransform

namespace Ws31
namespace MellinInv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def lineProfile (σ : ℝ) (a : ℝ → E) (y : ℝ) : E :=
  ∫ t : ℝ, (((y : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) • a t)

def HasIntegrableProfile (σ : ℝ) (b : ℝ → E) : Prop :=
  IntegrableOn (fun y : ℝ => ((y ^ (-σ) / y : ℝ) : ℂ) • lineProfile σ b y) (Set.Ioi (0 : ℝ))

def charIntegral (a : ℝ → E) (u : ℝ) : E :=
  ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) • a t

theorem cpow_exp_eq (σ u t : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)
      = ((Real.exp (σ * u) : ℝ) : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_exp, mul_add, Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_mul]
  congr 1 <;> (congr 1; ring)

theorem cpow_exp_eq_zero (u t : ℝ) :
    ((Real.exp u : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) = Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) := by
  have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le,
    Real.log_exp]
  congr 1
  push_cast
  ring

theorem lineProfile_exp (σ : ℝ) (a : ℝ → E) (u : ℝ) :
    lineProfile σ a (Real.exp u) = ((Real.exp (σ * u) : ℝ) : ℂ) • charIntegral a u := by
  unfold lineProfile charIntegral
  rw [← integral_smul]
  congr 1
  funext t
  rw [cpow_exp_eq, mul_smul]

theorem charIntegral_two_pi_mul (a : ℝ → E) (w : ℝ) : charIntegral a (2 * π * w) = 𝓕⁻ a w := by
  rw [fourierInv_eq']
  unfold charIntegral
  have h : ∀ t : ℝ, ((t * (2 * π * w) : ℝ) : ℂ) = ((2 * π * inner ℝ t w : ℝ) : ℂ) := fun t => by
    rw [Real.inner_apply]
    push_cast
    ring
  simp_rw [h]

theorem charIntegral_eq_integral_mul (b : ℝ → ℂ) (u : ℝ) :
    charIntegral b u = ∫ t : ℝ, Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * b t := by
  unfold charIntegral
  simp_rw [smul_eq_mul]

theorem HasIntegrableProfile.integrable_fourierInv {σ : ℝ} {b : ℝ → E}
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

theorem main (a : ℝ → ℂ) (ha : Integrable a) (hac : Continuous a)
    (hap : IntegrableOn (fun y : ℝ => ((y ^ (-(0 : ℝ)) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * a t) (Set.Ioi 0))
    (t₀ : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
        ∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t) = ((2 * Real.pi : ℝ) : ℂ) * a t₀ := by
  have h2π : (2 : ℝ) * π ≠ 0 := by positivity

  have hap' : HasIntegrableProfile 0 a := by
    unfold HasIntegrableProfile lineProfile
    simpa only [smul_eq_mul] using hap
  have hFa : Integrable (𝓕⁻ a) := hap'.integrable_fourierInv
  have hFa' : Integrable (𝓕 fun x : ℝ => a (-x)) := by
    rw [← fourierInv_eq_fourier_comp_neg a]
    exact hFa
  have hinv : 𝓕⁻ (𝓕 fun x : ℝ => a (-x)) = fun x : ℝ => a (-x) :=
    (hac.comp continuous_neg).fourierInv_fourier_eq ha.comp_neg hFa'

  have himage : Set.Ioi (0 : ℝ) = Real.exp '' Set.univ := by rw [Set.image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp Set.univ := fun _ _ _ _ h => Real.exp_injective h
  have hcollapse : ∀ u : ℝ, |Real.exp u| • ((((Real.exp u)⁻¹ : ℝ) : ℂ) *
      ((((Real.exp u : ℝ) : ℂ) ^ (-((t₀ : ℂ) * Complex.I))) *
        ∫ t : ℝ, ((Real.exp u : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) * a t))
      = Complex.exp ((((-t₀) * u : ℝ) : ℂ) * Complex.I) * charIntegral a u := by
    intro u
    have hker : ((Real.exp u : ℝ) : ℂ) ^ (-((t₀ : ℂ) * Complex.I))
        = Complex.exp ((((-t₀) * u : ℝ) : ℂ) * Complex.I) := by
      rw [show -((t₀ : ℂ) * Complex.I) = ((-t₀ : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact cpow_exp_eq_zero u (-t₀)
    have hprof : (∫ t : ℝ, ((Real.exp u : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) * a t) = charIntegral a u := by
      unfold charIntegral
      congr 1
      funext t
      rw [cpow_exp_eq_zero, smul_eq_mul]
    rw [hker, hprof, ← Complex.coe_smul, smul_eq_mul, abs_of_pos (Real.exp_pos u), ← mul_assoc,
      ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.exp_pos u).ne', Complex.ofReal_one, one_mul]
  have hc : ∀ w : ℝ, (((-t₀) * (2 * π * w) : ℝ) : ℂ) = ((w * (2 * π * (-t₀)) : ℝ) : ℂ) := fun w => by
    push_cast
    ring
  calc ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
          ∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t)
      = ∫ u : ℝ, Complex.exp ((((-t₀) * u : ℝ) : ℂ) * Complex.I) * charIntegral a u := by
        rw [himage, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
          Measure.restrict_univ]
        exact integral_congr_ae (Filter.Eventually.of_forall hcollapse)
    _ = |2 * π| • ∫ w : ℝ, Complex.exp ((((-t₀) * (2 * π * w) : ℝ) : ℂ) * Complex.I) *
          charIntegral a (2 * π * w) := by
        rw [Measure.integral_comp_mul_left
            (fun u : ℝ => Complex.exp ((((-t₀) * u : ℝ) : ℂ) * Complex.I) * charIntegral a u) (2 * π),
          smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr h2π), one_smul]
    _ = |2 * π| • 𝓕⁻ (𝓕⁻ a) (-t₀) := by
        congr 1
        rw [← charIntegral_two_pi_mul (𝓕⁻ a) (-t₀), charIntegral_eq_integral_mul (𝓕⁻ a)]
        simp_rw [charIntegral_two_pi_mul, hc]
    _ = |2 * π| • a t₀ := by
        rw [fourierInv_eq_fourier_comp_neg a, hinv]
        simp only [neg_neg]
    _ = ((2 * Real.pi : ℝ) : ℂ) * a t₀ := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Complex.real_smul]

end Ws31.MellinInv

end

open MeasureTheory
open scoped ComplexConjugate

theorem solution
    (a : ℝ → ℂ) (_ha : Integrable a) (_hac : Continuous a)
    (_hap : IntegrableOn (fun y : ℝ => ((y ^ (-(0 : ℝ)) / y : ℝ) : ℂ) *
        ∫ t : ℝ, (y : ℂ) ^ (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) * a t) (Set.Ioi 0))
    (t₀ : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((y : ℂ) ^ (-((t₀ : ℂ) * Complex.I)) *
        ∫ t : ℝ, (y : ℂ) ^ ((t : ℂ) * Complex.I) * a t) = ((2 * Real.pi : ℝ) : ℂ) * a t₀ :=
  Ws31.MellinInv.main a _ha _hac _hap t₀

end S_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul
end P2MW
export P2MW.S_MellinParseval_setIntegral_Ioi_inv_mul_cpow_neg_mul_lineIntegral_eq_two_pi_mul (solution)
