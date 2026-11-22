-- Prove2me | solution 1 for MasulloRH.digamma_real_place
-- status  : ACCEPTED   (prove)
-- author  : @cyw
-- created : 2026-11-21T00:28:58.46881+00:00
-- url     : https://prove2.me/submissions/95d0c830-10dd-4e4b-a8f0-e901205f7903

/-
Portions of the Fourier normalization and inversion are adapted from Zeta23/ExplicitFormula.lean.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
SPDX-License-Identifier: Apache-2.0
https://github.com/anthropics/formal-math/blob/main/zeta23/Zeta23/ExplicitFormula.lean
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Digamma and the real place in the rational trace formula

The Fourier normalization is the positive-sign convention of Zeta23.
The hypothesis `φ 1 = 0` removes the frequency-independent term.
-/

set_option autoImplicit false

open MeasureTheory Set

/-- Domination for the kernel in the real part of the digamma difference integral. -/
theorem gammaDifferenceKernel_weight_le {u : ℝ} (hu : 0 < u) :
    u ^ 2 * Real.exp (-(u / 4)) / (1 - Real.exp (-u)) ≤
      (u + u ^ 2) * Real.exp (-(u / 4)) := by
  have he := Real.exp_pos u
  have h1 := Real.add_one_le_exp u
  have hnegExp : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)
  have hden : 0 < 1 - Real.exp (-u) := sub_pos.mpr hnegExp
  rw [div_le_iff₀ hden]
  have hmul : (u + 1) * (Real.exp u)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_iff₀ he, one_mul]
    exact h1
  have hcancel : u ≤ (u + 1) * (1 - (Real.exp u)⁻¹) := by
    nlinarith
  rw [← Real.exp_neg] at hcancel
  calc
    u ^ 2 * Real.exp (-(u / 4)) = u * (u * Real.exp (-(u / 4))) := by ring
    _ ≤ ((u + 1) * (1 - Real.exp (-u))) * (u * Real.exp (-(u / 4))) :=
      mul_le_mul_of_nonneg_right hcancel (by positivity)
    _ = (u + u ^ 2) * Real.exp (-(u / 4)) * (1 - Real.exp (-u)) := by ring

/-- An integrable majorant for the (u)-variable in the archimedean Fourier calculation. -/
theorem gammaDifferenceKernel_weight_integrable :
    IntegrableOn (fun u : ℝ =>
      u ^ 2 * Real.exp (-(u / 4)) / (1 - Real.exp (-u))) (Ioi 0) := by
  have hfirst : IntegrableOn (fun u : ℝ => u * Real.exp (-(u / 4))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := 1 / 4)
      (by norm_num) (by norm_num) (by norm_num)
    convert h using 1
    ext u
    simp only [Real.rpow_one]
    congr 2
    ring
  have hsecond : IntegrableOn (fun u : ℝ => u ^ 2 * Real.exp (-(u / 4))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2) (b := 1 / 4)
      (by norm_num) (by norm_num) (by norm_num)
    convert h using 1
    ext u
    simp only [Real.rpow_one, Real.rpow_two]
    congr 2
    ring
  have hmeasurable : Measurable (fun u : ℝ =>
      u ^ 2 * Real.exp (-(u / 4)) / (1 - Real.exp (-u))) := by
    apply Measurable.div
    · exact (by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-(u / 4)))).measurable
    · exact (by fun_prop : Continuous (fun u : ℝ => 1 - Real.exp (-u))).measurable
  apply (hfirst.add hsecond).mono' hmeasurable.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
  change 0 < u at hu
  have hden : 0 < 1 - Real.exp (-u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  rw [Real.norm_of_nonneg (div_nonneg (by positivity) hden.le)]
  simpa only [Pi.add_apply, add_mul] using gammaDifferenceKernel_weight_le hu

/-- A quadratic bound that preserves integrability at the origin in the digamma kernel. -/
theorem one_sub_cos_le_half_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hcos : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    convert Real.cos_two_mul_eq_one_sub (x := x / 2) using 1
    ring_nf
  rw [hcos]
  nlinarith [Real.sin_sq_le_sq (x := x / 2)]

/-- Joint integrability for the archimedean Fourier calculation. -/
theorem integrable_gammaDifferenceKernel_mul_fourier (H : ℝ → ℂ)
    (hmeas : Measurable H)
    (hweighted : Integrable (fun r : ℝ => ‖H r‖ * r ^ 2)) :
    Integrable (fun p : ℝ × ℝ => H p.1 *
      ((Real.exp (-(p.2 / 4)) / (1 - Real.exp (-p.2)) *
        (1 - Real.cos (p.1 * p.2 / 2)) : ℝ) : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hmeasF : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(p.2 / 4)) / (1 - Real.exp (-p.2)) * (1 - Real.cos (p.1 * p.2 / 2))) := by
    apply Measurable.mul
    · apply Measurable.div
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(p.2 / 4))).measurable
      · exact (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.exp (-p.2)).measurable
    · exact (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2 / 2)).measurable
  have hprod := hweighted.mul_prod gammaDifferenceKernel_weight_integrable
  apply hprod.mono' ((hmeas.comp measurable_fst).mul
    (Complex.continuous_ofReal.measurable.comp hmeasF)).aestronglyMeasurable
  have haepos : ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))), 0 < p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).2
      (Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioi))
  filter_upwards [haepos] with p hu
  have hden : 0 < 1 - Real.exp (-p.2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  have hcos : 0 ≤ 1 - Real.cos (p.1 * p.2 / 2) := sub_nonneg.mpr (Real.cos_le_one _)
  have hcosBound : 1 - Real.cos (p.1 * p.2 / 2) ≤ p.1 ^ 2 * p.2 ^ 2 := by
    calc
      _ ≤ (p.1 * p.2 / 2) ^ 2 / 2 := one_sub_cos_le_half_sq _
      _ = p.1 ^ 2 * p.2 ^ 2 / 8 := by ring
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg p.1) (sq_nonneg p.2)]
  have hweight : 0 ≤ Real.exp (-(p.2 / 4)) / (1 - Real.exp (-p.2)) := by positivity
  change ‖H p.1 * ((Real.exp (-(p.2 / 4)) / (1 - Real.exp (-p.2)) *
    (1 - Real.cos (p.1 * p.2 / 2)) : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hweight hcos)]
  calc
    _ ≤ ‖H p.1‖ * ((Real.exp (-(p.2 / 4)) / (1 - Real.exp (-p.2))) *
        (p.1 ^ 2 * p.2 ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcosBound hweight) (norm_nonneg _)
    _ = _ := by ring

open scoped SchwartzMap FourierTransform ContDiff

/-- Squared-frequency integrability of the rescaled Fourier transform of a compact smooth test. -/
theorem integrable_weighted_scaled_fourier_of_smooth_compact {k : ℝ → ℂ}
    (hkc : HasCompactSupport k) (hks : ContDiff ℝ ∞ k) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun r : ℝ => ‖𝓕 k (a * r)‖ * r ^ 2) := by
  let s : 𝓢(ℝ, ℂ) := hkc.toSchwartzMap hks
  let g : 𝓢(ℝ, ℂ) := 𝓕 s
  have hg (x : ℝ) : g x = 𝓕 k x := congrFun (SchwartzMap.fourier_coe s) x
  have h := ((g.integrable_pow_mul volume 2).comp_mul_left' ha).const_mul (a ^ 2)⁻¹
  refine h.congr ?_
  filter_upwards with r
  change (a ^ 2)⁻¹ * (‖a * r‖ ^ 2 * ‖g (a * r)‖) = ‖𝓕 k (a * r)‖ * r ^ 2
  rw [hg, Real.norm_eq_abs, sq_abs, mul_pow]
  calc
    _ = ((a ^ 2)⁻¹ * a ^ 2) * (‖𝓕 k (a * r)‖ * r ^ 2) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero _ ha), one_mul]

noncomputable def gammaGaussWeight (u : ℝ) : ℝ :=
  Real.exp (-(u / 4)) / (1 - Real.exp (-u))

noncomputable def gammaGaussKernel (r u : ℝ) : ℝ :=
  gammaGaussWeight u * (1 - Real.cos (r * u / 2))

/-- Convert a Gauss digamma-difference integral into the logarithmic real-place term. -/
theorem gammaGaussIntegral_eq_neg_log_trace
    (H k : ℝ → ℂ) (Γ : ℝ → ℝ)
    (hmeas : Measurable H) (hH : Integrable H)
    (hweighted : Integrable (fun r : ℝ => ‖H r‖ * r ^ 2))
    (hΓ : ∀ r, Γ r - Γ 0 = ∫ u in Ioi (0 : ℝ), gammaGaussKernel r u)
    (hzero : (∫ r : ℝ, H r) = 0)
    (hcos : ∀ u : ℝ,
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ r : ℝ, H r * ((1 - Real.cos (r * u / 2) : ℝ) : ℂ)) =
        -(k (u / 2) + k (-(u / 2))) / 2) :
    (1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, H r * (Γ r : ℂ)) =
      -(∫ x in Ioi (0 : ℝ), (k x + k (-x)) *
        ((Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) : ℝ) : ℂ)) := by
  let F : ℝ → ℝ → ℂ := fun r u => H r * (gammaGaussKernel r u : ℂ)
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  change c * _ = _
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_gammaDifferenceKernel_mul_fourier H hmeas hweighted
  have hsplit (r : ℝ) : H r * (Γ r : ℂ) = H r * (Γ 0 : ℂ) + ∫ u in Ioi (0 : ℝ), F r u := by
    have hΓr : Γ r = Γ 0 + ∫ u in Ioi (0 : ℝ), gammaGaussKernel r u := by
      linarith [hΓ r]
    rw [hΓr, Complex.ofReal_add, integral_const_mul, integral_complex_ofReal, mul_add]
  have hF_eval (u : ℝ) : c * (∫ r : ℝ, F r u) =
      -((k (u / 2) + k (-(u / 2))) / 2 * (gammaGaussWeight u : ℂ)) := by
    have hrearrange (r : ℝ) : F r u =
        H r * ((1 - Real.cos (r * u / 2) : ℝ) : ℂ) * (gammaGaussWeight u : ℂ) := by
      simp only [F, gammaGaussKernel, Complex.ofReal_mul]
      ring
    simp_rw [hrearrange]
    rw [integral_mul_const, ← mul_assoc]
    change (1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, H r *
      ((1 - Real.cos (r * u / 2) : ℝ) : ℂ)) * (gammaGaussWeight u : ℂ) = _
    rw [hcos]
    ring
  rw [show (fun r : ℝ => H r * (Γ r : ℂ)) =
    (fun r : ℝ => H r * (Γ 0 : ℂ) + ∫ u in Ioi (0 : ℝ), F r u) from funext hsplit]
  have hinner : Integrable (fun r => ∫ u in Ioi (0 : ℝ), F r u) := hF.integral_prod_left
  rw [integral_add (hH.mul_const (Γ 0 : ℂ)) hinner, integral_mul_const, hzero, zero_mul, zero_add,
    integral_integral_swap hF, ← integral_const_mul]
  simp_rw [hF_eval]
  rw [integral_neg]
  congr 1
  let g : ℝ → ℂ := fun u => (k (u / 2) + k (-(u / 2))) / 2 * (gammaGaussWeight u : ℂ)
  change (∫ u in Ioi (0 : ℝ), g u) = _
  have hscale := integral_comp_mul_left_Ioi' g 0 (b := 2) (by norm_num)
  rw [mul_zero] at hscale
  rw [← hscale, Complex.real_smul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp only [g, gammaGaussWeight]
  rw [show (2 : ℝ) * x / 2 = x by ring, show (2 : ℝ) * x / 4 = x / 2 by ring]
  push_cast
  ring

/-- The weighted Fourier integral against a bracket with the Gauss difference formula exists. -/
theorem integrable_fourier_mul_of_gammaGaussIntegral
    (H : ℝ → ℂ) (Γ : ℝ → ℝ)
    (hmeas : Measurable H) (hH : Integrable H)
    (hweighted : Integrable (fun r : ℝ => ‖H r‖ * r ^ 2))
    (hΓ : ∀ r, Γ r - Γ 0 = ∫ u in Ioi (0 : ℝ), gammaGaussKernel r u) :
    Integrable (fun r : ℝ => H r * (Γ r : ℂ)) := by
  let F : ℝ → ℝ → ℂ := fun r u => H r * (gammaGaussKernel r u : ℂ)
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_gammaDifferenceKernel_mul_fourier H hmeas hweighted
  have hinner : Integrable (fun r => ∫ u in Ioi (0 : ℝ), F r u) := hF.integral_prod_left
  refine ((hH.mul_const (Γ 0 : ℂ)).add hinner).congr (Filter.Eventually.of_forall fun r => ?_)
  change H r * (Γ 0 : ℂ) + (∫ u in Ioi (0 : ℝ), F r u) = H r * (Γ r : ℂ)
  have hΓr : Γ r = Γ 0 + ∫ u in Ioi (0 : ℝ), gammaGaussKernel r u := by linarith [hΓ r]
  symm
  rw [hΓr, Complex.ofReal_add, integral_const_mul, integral_complex_ofReal, mul_add]

/-- The real-place kernel is integrable under the weighted Fourier and inversion hypotheses. -/
theorem integrableOn_log_trace_of_cosine_inversion
    (H k : ℝ → ℂ) (hmeas : Measurable H)
    (hweighted : Integrable (fun r : ℝ => ‖H r‖ * r ^ 2))
    (hcos : ∀ u : ℝ,
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ r : ℝ, H r * ((1 - Real.cos (r * u / 2) : ℝ) : ℂ)) =
        -(k (u / 2) + k (-(u / 2))) / 2) :
    IntegrableOn (fun x : ℝ => (k x + k (-x)) *
      ((Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) : ℝ) : ℂ)) (Ioi 0) := by
  let F : ℝ → ℝ → ℂ := fun r u => H r * (gammaGaussKernel r u : ℂ)
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  let g : ℝ → ℂ := fun u => (k (u / 2) + k (-(u / 2))) / 2 * (gammaGaussWeight u : ℂ)
  have hF : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) :=
    integrable_gammaDifferenceKernel_mul_fourier H hmeas hweighted
  have hinner : IntegrableOn (fun u => ∫ r : ℝ, F r u) (Ioi 0) := hF.integral_prod_right
  have hg : IntegrableOn g (Ioi 0) := by
    refine (hinner.const_mul (-c)).congr (Filter.Eventually.of_forall fun u => ?_)
    change (-c) * (∫ r : ℝ, F r u) = g u
    have hrearrange (r : ℝ) : F r u =
        H r * ((1 - Real.cos (r * u / 2) : ℝ) : ℂ) * (gammaGaussWeight u : ℂ) := by
      simp only [F, gammaGaussKernel, Complex.ofReal_mul]
      ring
    simp_rw [hrearrange]
    rw [integral_mul_const, neg_mul, ← mul_assoc]
    change -((1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, H r *
      ((1 - Real.cos (r * u / 2) : ℝ) : ℂ)) * (gammaGaussWeight u : ℂ)) = _
    rw [hcos]
    unfold g
    ring
  have hscaled : IntegrableOn (fun x : ℝ => g (2 * x)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 (a := 2) (by norm_num)).2
    simpa only [mul_zero] using hg
  refine (hscaled.const_mul (2 : ℂ)).congr (Filter.Eventually.of_forall fun x => ?_)
  change 2 * g (2 * x) = _
  simp only [g, gammaGaussWeight]
  rw [show (2 : ℝ) * x / 2 = x by ring, show (2 : ℝ) * x / 4 = x / 2 by ring]
  ring

open Complex Filter MeasureTheory Set
open scoped Topology

namespace DigammaGauss

private theorem gammaRatio_hasDerivAt {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => Gamma z / Gamma (w + z)) (-digamma z) 0 := by
  have hznp (n : ℕ) : z ≠ -(n : ℂ) := by
    intro h
    have hre := congrArg re h
    simp at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hΓ := Gamma_ne_zero_of_re_pos hz
  have hd : HasDerivAt Gamma (deriv Gamma z) ((0 : ℂ) + z) := by
    simpa using (differentiableAt_Gamma z hznp).hasDerivAt
  have h := (hasDerivAt_const (0 : ℂ) (Gamma z)).div (hd.comp_add_const 0 z)
    (by simpa using hΓ)
  have hcoeff : (0 * Gamma (0 + z) - Gamma z * deriv Gamma z) / Gamma (0 + z) ^ 2 =
      -digamma z := by
    rw [digamma_def, logDeriv_apply]
    simp only [zero_add, zero_mul, zero_sub]
    field_simp
  rw [hcoeff] at h
  exact h

noncomputable def betaStep (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem betaStep_pos (n : ℕ) : 0 < betaStep n := by unfold betaStep; positivity

theorem tendsto_betaStep : Tendsto betaStep atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

theorem tendsto_betaDifference {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    Tendsto (fun n => betaIntegral a (betaStep n) - betaIntegral z (betaStep n))
      atTop (𝓝 (digamma z - digamma a)) := by
  let G : ℂ → ℂ := fun w => Gamma a / Gamma (w + a) - Gamma z / Gamma (w + z)
  have hderiv : HasDerivAt G (digamma z - digamma a) 0 := by
    simpa only [G, sub_neg_eq_add, neg_add_eq_sub] using
      (gammaRatio_hasDerivAt ha).fun_sub (gammaRatio_hasDerivAt hz)
  have hG0 : G 0 = 0 := by
    simp [G, Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hz]
  have ht : Tendsto (fun n => (betaStep n : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa [Function.comp_def] using (continuous_ofReal.continuousAt (x := (0 : ℝ)).tendsto.comp tendsto_betaStep)
  have htne : Tendsto (fun n => (betaStep n : ℂ)) atTop (𝓝[≠] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall fun n => by
      simpa using (betaStep_pos n).ne'⟩
  have hslope := hderiv.tendsto_slope_zero.comp htne
  have hΓ : Tendsto (fun n => Gamma ((betaStep n : ℂ) + 1)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using continuousAt_Gamma_one.tendsto.comp (by simpa using ht.add_const (1 : ℂ))
  have hfinal := hΓ.mul hslope
  simp only [one_mul] at hfinal
  refine hfinal.congr fun n => ?_
  have hpos : 0 < (betaStep n : ℂ).re := by simp [betaStep_pos n]
  have hne : (betaStep n : ℂ) ≠ 0 := by simpa using (betaStep_pos n).ne'
  change Gamma ((betaStep n : ℂ) + 1) *
    ((betaStep n : ℂ)⁻¹ • (G (0 + (betaStep n : ℂ)) - G 0)) = _
  rw [Gamma_add_one _ hne, hG0, sub_zero, zero_add, smul_eq_mul,
    betaIntegral_eq_Gamma_mul_div _ _ ha hpos, betaIntegral_eq_Gamma_mul_div _ _ hz hpos]
  simp only [G, add_comm a (betaStep n : ℂ), add_comm z (betaStep n : ℂ)]
  calc
    _ = Gamma (betaStep n) *
          (Gamma a / Gamma ((betaStep n : ℂ) + a) - Gamma z / Gamma ((betaStep n : ℂ) + z)) := by
      calc
        _ = ((betaStep n : ℂ) * (betaStep n : ℂ)⁻¹) * (Gamma (betaStep n) *
          (Gamma a / Gamma ((betaStep n : ℂ) + a) - Gamma z / Gamma ((betaStep n : ℂ) + z))) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hne, one_mul]
    _ = _ := by ring

noncomputable def betaExpKernel (z : ℂ) (w u : ℝ) : ℂ :=
  Complex.exp (-(u : ℂ) * z) * ((1 - Real.exp (-u)) ^ (w - 1) : ℝ)

theorem betaIntegral_eq_expKernel {z : ℂ} {w : ℝ} (hz : 0 < z.re) (hw : 0 < w) :
    IntegrableOn (betaExpKernel z w) (Ioi 0) ∧
      betaIntegral z w = ∫ u in Ioi (0 : ℝ), betaExpKernel z w u := by
  let f : ℝ → ℝ := fun u => Real.exp (-u)
  let df : ℝ → ℝ := fun u => -Real.exp (-u)
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (z - 1) * (1 - (t : ℂ)) ^ ((w : ℂ) - 1)
  have himg : f '' Ioi 0 = Ioo 0 1 := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)⟩
    · rintro ⟨hy, hlt⟩
      exact ⟨-Real.log y, neg_pos.mpr (Real.log_neg hy hlt), by simpa [f] using Real.exp_log hy⟩
  have hdiff : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt f (df u) (Ioi 0) u := by
    intro u _
    have h := (Real.hasDerivAt_exp (-u)).comp u ((hasDerivAt_id u).neg)
    simpa [f, df, Function.comp_def] using h.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn f (Ioi 0) := Real.exp_injective.comp neg_injective |>.injOn
  have hint : IntegrableOn g (Ioo 0 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    exact betaIntegral_convergent hz (by simpa using hw)
  have hf : ∀ u ∈ Ioi (0 : ℝ), |df u| • g (f u) = betaExpKernel z w u := by
    intro u hu
    have hnonneg : 0 ≤ 1 - Real.exp (-u) := by
      exact sub_nonneg.mpr ((Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu)).le)
    have hp : (Real.exp (-u) : ℂ) ^ (z - 1) =
        Complex.exp (-(u : ℂ) * (z - 1)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
        ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_neg]
    have hc : ((1 - Real.exp (-u)) ^ (w - 1) : ℝ) =
        (1 - (Real.exp (-u) : ℂ)) ^ ((w : ℂ) - 1) := by
      simpa using Complex.ofReal_cpow hnonneg (w - 1)
    change |-(Real.exp (-u))| • ((Real.exp (-u) : ℂ) ^ (z - 1) *
      (1 - (Real.exp (-u) : ℂ)) ^ ((w : ℂ) - 1)) = _
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul,
      hp, ← hc, betaExpKernel, ← mul_assoc, Complex.ofReal_exp, Complex.ofReal_neg, ← Complex.exp_add]
    congr 2
    ring
  refine ⟨?_, ?_⟩
  · rw [← himg] at hint
    have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hdiff hinj g).mp hint
    exact hj.congr_fun hf measurableSet_Ioi
  · rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    change (∫ t in Ioo (0 : ℝ) 1, g t) = _
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hdiff hinj]
    exact setIntegral_congr_fun measurableSet_Ioi hf

noncomputable def betaRealKernel (r w u : ℝ) : ℝ :=
  Real.exp (-(u / 4)) * (1 - Real.exp (-u)) ^ (w - 1) * (1 - Real.cos (r * u / 2))

theorem betaDifference_re_eq_integral (r : ℝ) {w : ℝ} (hw : 0 < w) :
    (betaIntegral (1 / 4) w - betaIntegral (1 / 4 + (r : ℂ) * I / 2) w).re =
      ∫ u in Ioi (0 : ℝ), betaRealKernel r w u := by
  have ha : 0 < (1 / 4 : ℂ).re := by norm_num
  have hz : 0 < (1 / 4 + (r : ℂ) * I / 2).re := by simp
  obtain ⟨h₁, he₁⟩ := betaIntegral_eq_expKernel ha hw
  obtain ⟨h₂, he₂⟩ := betaIntegral_eq_expKernel hz hw
  have hre : (∫ u in Ioi (0 : ℝ),
      (betaExpKernel (1 / 4) w u - betaExpKernel (1 / 4 + (r : ℂ) * I / 2) w u).re) =
      (∫ u in Ioi (0 : ℝ),
        betaExpKernel (1 / 4) w u - betaExpKernel (1 / 4 + (r : ℂ) * I / 2) w u).re :=
    Complex.reCLM.integral_comp_comm (h₁.sub h₂)
  rw [he₁, he₂, ← integral_sub h₁ h₂, ← hre]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [betaExpKernel, betaRealKernel, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hbase : -(u : ℂ) * (1 / 4 : ℂ) = ((-(u / 4) : ℝ) : ℂ) := by push_cast; ring
  have hzarg : -(u : ℂ) * (1 / 4 + (r : ℂ) * I / 2) =
      ((-(u / 4) : ℝ) : ℂ) + ((-(r * u / 2) : ℝ) : ℂ) * I := by push_cast; ring
  rw [hbase, hzarg]
  simp only [Complex.exp_re, Complex.ofReal_re, Complex.ofReal_im, Real.cos_zero, mul_one,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, zero_add, Real.cos_neg]
  ring

theorem digamma_re_sub_eq_integral (r : ℝ) :
    (Complex.digamma (1 / 4 + (r : ℂ) * Complex.I / 2)).re - (Complex.digamma (1 / 4)).re =
      ∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-(u / 4)) / (1 - Real.exp (-u)) * (1 - Real.cos (r * u / 2)) := by
  let K : ℝ → ℝ := fun u =>
    Real.exp (-(u / 4)) / (1 - Real.exp (-u)) * (1 - Real.cos (r * u / 2))
  have hβ := tendsto_betaDifference (a := 1 / 4) (z := 1 / 4 + (r : ℂ) * I / 2)
    (by norm_num) (by simp)
  have hlβ : Tendsto (fun n => ∫ u in Ioi (0 : ℝ), betaRealKernel r (betaStep n) u)
      atTop (𝓝 ((digamma (1 / 4 + (r : ℂ) * I / 2)).re - (digamma (1 / 4)).re)) := by
    have h : Tendsto
        (fun n => (betaIntegral (1 / 4) (betaStep n) -
          betaIntegral (1 / 4 + (r : ℂ) * I / 2) (betaStep n)).re)
        atTop (𝓝 ((digamma (1 / 4 + (r : ℂ) * I / 2) - digamma (1 / 4)).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp hβ
    rw [Complex.sub_re] at h
    exact h.congr (fun n => betaDifference_re_eq_integral r (betaStep_pos n))
  have hbase {u : ℝ} (hu : 0 < u) : 0 < 1 - Real.exp (-u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hu))
  have hK : Tendsto (fun n => ∫ u in Ioi (0 : ℝ), betaRealKernel r (betaStep n) u)
      atTop (𝓝 (∫ u in Ioi (0 : ℝ), K u)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun u => r ^ 2 * (u ^ 2 * Real.exp (-(u / 4)) / (1 - Real.exp (-u))))
    · intro n
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro u hu
      have hOuter : ContinuousAt (fun t : ℝ => t ^ (betaStep n - 1)) (1 - Real.exp (-u)) :=
        Real.continuousAt_rpow_const _ _ (Or.inl (hbase hu).ne')
      have hInner : ContinuousAt (fun t : ℝ => 1 - Real.exp (-t)) u := by fun_prop
      have hpow : ContinuousAt (fun t : ℝ => (1 - Real.exp (-t)) ^ (betaStep n - 1)) u :=
        ContinuousAt.comp (f := fun t : ℝ => 1 - Real.exp (-t))
          (g := fun t : ℝ => t ^ (betaStep n - 1)) (x := u) hOuter hInner
      apply ContinuousAt.continuousWithinAt
      unfold betaRealKernel
      fun_prop
    · exact gammaDifferenceKernel_weight_integrable.const_mul (r ^ 2)
    · intro n
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
      have hc := hbase hu
      have hc1 : (1 - Real.exp (-u)) ≤ 1 := sub_le_self _ (Real.exp_pos _).le
      have hp : (1 - Real.exp (-u)) ^ (betaStep n - 1) ≤ (1 - Real.exp (-u))⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_ge hc hc1 (by linarith [betaStep_pos n])
      have hcos : 0 ≤ 1 - Real.cos (r * u / 2) := sub_nonneg.mpr (Real.cos_le_one _)
      have hcosBound : 1 - Real.cos (r * u / 2) ≤ r ^ 2 * u ^ 2 := by
        calc
          _ ≤ (r * u / 2) ^ 2 / 2 := one_sub_cos_le_half_sq _
          _ = r ^ 2 * u ^ 2 / 8 := by ring
          _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg u)]
      unfold betaRealKernel
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg hc.le _)) hcos)]
      calc
        _ ≤ Real.exp (-(u / 4)) * (1 - Real.exp (-u))⁻¹ * (1 - Real.cos (r * u / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le) hcos
        _ ≤ Real.exp (-(u / 4)) * (1 - Real.exp (-u))⁻¹ * (r ^ 2 * u ^ 2) :=
          mul_le_mul_of_nonneg_left hcosBound (by positivity)
        _ = _ := by ring
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with u hu
      have hc := hbase hu
      have hi : Tendsto (fun n => (1 - Real.exp (-u)) ^ (betaStep n - 1)) atTop
          (𝓝 ((1 - Real.exp (-u))⁻¹)) := by
        have hstep : Tendsto (fun n => betaStep n - 1) atTop (𝓝 (-1 : ℝ)) := by
          simpa using tendsto_betaStep.sub_const (1 : ℝ)
        simpa only [Function.comp_def, Real.rpow_neg_one] using
          (Real.continuousAt_const_rpow hc.ne').tendsto.comp hstep
      simpa only [betaRealKernel, K, div_eq_mul_inv] using
        (hi.const_mul (Real.exp (-(u / 4)))).mul_const (1 - Real.cos (r * u / 2))
  exact tendsto_nhds_unique hlβ hK


end DigammaGauss

open MeasureTheory
open scoped SchwartzMap FourierTransform ContDiff

namespace MasulloRHProof

/-- Positive-sign Fourier transform in the normalization of the explicit formula. -/
noncomputable def literatureFT (k : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, k x * Complex.exp (Complex.I * z * (x : ℂ))

private theorem literatureFT_scale (k : ℝ → ℂ) (r : ℝ) :
    literatureFT k r = 𝓕 k ((-(1 / (2 * Real.pi))) * r) := by
  rw [Real.fourier_real_eq_integral_exp_smul, literatureFT]
  congr 1
  ext x
  rw [smul_eq_mul, mul_comm (k x)]
  congr 1
  have hs : -2 * Real.pi * x * (-(1 / (2 * Real.pi)) * r) = r * x := by
    calc
      _ = (2 * Real.pi * (2 * Real.pi)⁻¹) * (r * x) := by
        simp only [one_div]
        ring
      _ = _ := by rw [mul_inv_cancel₀ (by positivity), one_mul]
  rw [hs]
  push_cast
  ring

private theorem literatureFT_inv {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (x : ℝ) :
    k x = (1 / (2 * (Real.pi : ℂ))) *
      ∫ r : ℝ, literatureFT k r * Complex.exp (-Complex.I * r * x) := by
  have hinv := congrFun (hk.fourierInv_fourier_eq hki hFk) x
  rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  let f : ℝ → ℂ := fun v => 𝓕 k v * Complex.exp (2 * Real.pi * Complex.I * v * x)
  have hscale (r : ℝ) :
      literatureFT k r * Complex.exp (-Complex.I * r * x) =
        f ((-(1 / (2 * Real.pi))) * r) := by
    rw [literatureFT_scale]
    unfold f
    congr 2
    push_cast
    field_simp
  simp_rw [hscale]
  rw [Measure.integral_comp_mul_left f]
  have hinvScale : |(-(1 / (2 * Real.pi)) : ℝ)⁻¹| = 2 * Real.pi := by
    rw [inv_neg, abs_neg, one_div, inv_inv, abs_of_pos (by positivity)]
  rw [hinvScale, Complex.real_smul, ← mul_assoc]
  have hc : (1 / (2 * (Real.pi : ℂ))) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  rw [hc, one_mul]
  congr 1
  ext v
  rw [smul_eq_mul, mul_comm]
  unfold f
  congr 2
  push_cast
  ring

theorem literatureFT_inversion_data {k : ℝ → ℂ} (hks : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (hk0 : k 0 = 0) :
    Measurable (fun r : ℝ => literatureFT k r) ∧
    Integrable (fun r : ℝ => literatureFT k r) ∧
    (∫ r : ℝ, literatureFT k r) = 0 ∧
    ∀ u : ℝ, (1 / (2 * (Real.pi : ℂ))) *
      (∫ r : ℝ, literatureFT k r * ((1 - Real.cos (r * u / 2) : ℝ) : ℂ)) =
        -(k (u / 2) + k (-(u / 2))) / 2 := by
  let s : 𝓢(ℝ, ℂ) := hkc.toSchwartzMap hks
  let g : 𝓢(ℝ, ℂ) := 𝓕 s
  have hg (x : ℝ) : g x = 𝓕 k x := congrFun (SchwartzMap.fourier_coe s) x
  have hFk : Integrable (𝓕 k) := by
    rw [← funext hg]
    exact g.integrable
  have hsc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hcont : Continuous (fun r : ℝ => literatureFT k r) := by
    simp_rw [literatureFT_scale, ← hg]
    exact g.continuous.comp (continuous_const.mul continuous_id)
  have hi : Integrable (fun r : ℝ => literatureFT k r) := by
    simpa only [literatureFT_scale] using hFk.comp_mul_left' hsc
  have hiK : Integrable k := hks.continuous.integrable_of_hasCompactSupport hkc
  have inv := literatureFT_inv hks.continuous hiK hFk
  let c : ℂ := 1 / (2 * (Real.pi : ℂ))
  have hz : c * (∫ r : ℝ, literatureFT k r) = 0 := by
    simpa [hk0, c] using (inv 0).symm
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
  have hzero := (mul_eq_zero.mp hz).resolve_left hc
  refine ⟨hcont.measurable, hi, hzero, fun u => ?_⟩
  let x : ℝ := u / 2
  have hcosMul : Integrable (fun r : ℝ => literatureFT k r * (Real.cos (r * x) : ℂ)) := by
    refine hi.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with r
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (r * x)
  have hexpMul (y : ℝ) :
      Integrable (fun r : ℝ => literatureFT k r * Complex.exp (-Complex.I * r * y)) := by
    refine hi.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with r
    simp [Complex.norm_exp]
  have hcosAdd (r : ℝ) :
      literatureFT k r * Complex.exp (-Complex.I * r * x) +
        literatureFT k r * Complex.exp (-Complex.I * r * ↑(-x)) =
        2 * (literatureFT k r * (Real.cos (r * x) : ℂ)) := by
    rw [← mul_add, Complex.ofReal_cos, mul_left_comm, Complex.two_cos, add_comm]
    congr 2
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  have hpair : k x + k (-x) =
      c * (2 * ∫ r : ℝ, literatureFT k r * (Real.cos (r * x) : ℂ)) := by
    rw [inv x, inv (-x), ← mul_add, ← integral_add (hexpMul x) (hexpMul (-x))]
    simp_rw [hcosAdd]
    rw [integral_const_mul]
  simp_rw [show ∀ r : ℝ, r * u / 2 = r * x from fun r => by dsimp [x]; ring,
    Complex.ofReal_sub, Complex.ofReal_one, mul_sub, mul_one]
  rw [integral_sub hi hcosMul, hzero, zero_sub]
  change c * (-(∫ r : ℝ, literatureFT k r * (Real.cos (r * x) : ℂ))) =
    -(k x + k (-x)) / 2
  rw [hpair]
  ring

end MasulloRHProof

open MeasureTheory Set
open scoped ContDiff

namespace MasulloRHProof

def IsRationalTraceTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 ∧ φ 1 = 0


noncomputable def realTraceIntegrand (φ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (φ t + φ t⁻¹) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)


/-- The logarithmic pullback is an admissible compact smooth test for the full explicit formula. -/
theorem logTraceTest {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    ContDiff ℝ ∞ (fun x => φ (Real.exp x)) ∧
      HasCompactSupport (fun x => φ (Real.exp x)) ∧ φ (Real.exp 0) = 0 := by
  obtain ⟨hsmooth, hcompact, hpositive, hzero⟩ := hφ
  refine ⟨hsmooth.comp Real.contDiff_exp, ?_, by simpa only [Real.exp_zero]⟩
  have hlog : ContinuousOn Real.log (tsupport φ) :=
    Real.continuousOn_log.mono (fun _ hx => ne_of_gt (hpositive hx))
  have hlogCompact := hcompact.image_of_continuousOn hlog
  exact hlogCompact.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx =>
    ⟨Real.exp x, subset_closure hx, Real.log_exp x⟩) hlogCompact.isClosed)

/-- Identifies the mission's shifted Mellin value with the log-coordinate Laplace integral. -/
theorem mellin_eq_logIntegral (φ : ℝ → ℂ) (z : ℂ) :
    mellin φ z = ∫ x : ℝ, Complex.exp ((x : ℂ) * z) * φ (Real.exp x) := by
  have hj := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t : ℝ => (t : ℂ) ^ (z - 1) • φ t)
  rw [image_univ, Real.range_exp, setIntegral_univ] at hj
  rw [mellin, hj]
  apply integral_congr_ae
  filter_upwards with x
  rw [abs_of_pos (Real.exp_pos x), Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Converts the literature Fourier transform on the log test to the mission's Mellin transform. -/
theorem literatureFT_eq_mellin (φ : ℝ → ℂ) (z : ℂ) :
    literatureFT (fun x => φ (Real.exp x)) z = mellin φ (Complex.I * z) := by
  rw [mellin_eq_logIntegral, literatureFT]
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm (φ (Real.exp x)), mul_comm (Complex.I * z)]


/-- Transform the real-place integrand by the positive exponential chart. -/
private theorem logTrace_kernel (φ : ℝ → ℂ) {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    |Real.exp x| • realTraceIntegrand φ (Real.exp x) =
      (φ (Real.exp x) + φ (Real.exp (-x))) *
        ((Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) : ℝ) : ℂ) := by
  have he : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hpos := Real.exp_pos x
  have hden : Real.exp x ^ 2 - 1 ≠ 0 := by
    have h : 0 < Real.exp x ^ 2 - 1 := by nlinarith
    exact ne_of_gt h
  have hpow : Real.exp x ^ 2 ≠ 0 := pow_ne_zero _ hpos.ne'
  have hexp : Real.exp (-(2 * x)) = (Real.exp x ^ 2)⁻¹ := by
    rw [Real.exp_neg, pow_two, ← Real.exp_add]
    congr 2
    ring
  have hnum : Real.exp x * Real.exp (x / 2) =
      Real.exp (-(x / 2)) * Real.exp x ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hratio : Real.exp x * (Real.sqrt (Real.exp x) / (Real.exp x ^ 2 - 1)) =
      Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) := by
    rw [← Real.exp_half, ← mul_div_assoc, hnum, hexp]
    have hinv : 1 - (Real.exp x ^ 2)⁻¹ ≠ 0 := by
      intro hzero
      apply hden
      have hb : (1 - (Real.exp x ^ 2)⁻¹) * Real.exp x ^ 2 = Real.exp x ^ 2 - 1 := by
        field_simp
      simpa [hzero] using hb.symm
    field_simp
  rw [abs_of_pos hpos, Complex.real_smul, realTraceIntegrand, ← Real.exp_neg]
  rw [← hratio, Complex.ofReal_mul]
  ring


/-- The mission's real-place integral in log coordinates. -/
theorem realTraceIntegral_eq_logIntegral (φ : ℝ → ℂ) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) =
      ∫ x in Ioi (0 : ℝ), (φ (Real.exp x) + φ (Real.exp (-x))) *
        ((Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) : ℝ) : ℂ) := by
  have hj := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (realTraceIntegrand φ)
  rw [Real.image_exp_Ioi, Real.exp_zero] at hj
  rw [hj]
  exact setIntegral_congr_fun measurableSet_Ioi (fun _ hx => logTrace_kernel φ hx)

/-- Integrability of the real-place kernel in either coordinate system. -/
private theorem integrableOn_realTrace_iff_logTrace (φ : ℝ → ℂ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ↔
      IntegrableOn (fun x => (φ (Real.exp x) + φ (Real.exp (-x))) *
        ((Real.exp (-(x / 2)) / (1 - Real.exp (-(2 * x))) : ℝ) : ℂ)) (Ioi 0) := by
  have hj := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (realTraceIntegrand φ)
  rw [Real.image_exp_Ioi, Real.exp_zero] at hj
  rw [hj]
  constructor
  · exact fun h => h.congr_fun (fun _ hx => logTrace_kernel φ hx) measurableSet_Ioi
  · exact fun h => h.congr_fun (fun _ hx => (logTrace_kernel φ hx).symm) measurableSet_Ioi

end MasulloRHProof

open MeasureTheory Set
open scoped ContDiff FourierTransform

namespace MasulloRHProof

/-- The Archimedean multiplier in Weil's explicit formula for the zeta function. -/
noncomputable def zetaGammaBracket (r : ℝ) : ℝ :=
  (Complex.digamma (1 / 4 + (r : ℂ) * Complex.I / 2)).re - Real.log Real.pi

private theorem digammaArchimedean_eq_realTrace_of_gauss
    (hGauss : ∀ r, zetaGammaBracket r - zetaGammaBracket 0 =
      ∫ u in Ioi (0 : ℝ), gammaGaussKernel r u)
    {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    Integrable (fun r : ℝ => mellin φ (Complex.I * r) * (zetaGammaBracket r : ℂ)) ∧
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ r : ℝ, mellin φ (Complex.I * r) * (zetaGammaBracket r : ℂ)) =
      -(∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) := by
  let k : ℝ → ℂ := fun x => φ (Real.exp x)
  let H : ℝ → ℂ := fun r => literatureFT k r
  obtain ⟨hks, hkc, hk0⟩ := logTraceTest hφ
  obtain ⟨hm, hi, hzero, hcos⟩ := literatureFT_inversion_data hks hkc hk0
  have hweighted : Integrable (fun r : ℝ => ‖H r‖ * r ^ 2) := by
    have ha : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
    simpa only [H, literatureFT_scale] using
      integrable_weighted_scaled_fourier_of_smooth_compact hkc hks ha
  have hM (r : ℝ) : H r = mellin φ (Complex.I * r) := literatureFT_eq_mellin φ r
  simp_rw [← hM]
  refine ⟨integrable_fourier_mul_of_gammaGaussIntegral H zetaGammaBracket hm hi hweighted hGauss,
    (integrableOn_realTrace_iff_logTrace φ).2
      (integrableOn_log_trace_of_cosine_inversion H k hm hweighted hcos), ?_⟩
  rw [realTraceIntegral_eq_logIntegral]
  exact gammaGaussIntegral_eq_neg_log_trace H k zetaGammaBracket hm hi hweighted
    hGauss hzero hcos

end MasulloRHProof

namespace MasulloRHProof

/-- Weil's archimedean term equals minus the rational trace formula's real-place integral. -/
theorem digammaArchimedean_eq_realTrace
    {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    Integrable (fun r : ℝ => mellin φ (Complex.I * r) * (zetaGammaBracket r : ℂ)) ∧
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    (1 / (2 * (Real.pi : ℂ))) *
      (∫ r : ℝ, mellin φ (Complex.I * r) * (zetaGammaBracket r : ℂ)) =
      -(∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) := by
  apply digammaArchimedean_eq_realTrace_of_gauss _ hφ
  intro r
  have h := DigammaGauss.digamma_re_sub_eq_integral r
  simpa only [zetaGammaBracket, Complex.ofReal_zero, zero_mul, zero_div, add_zero,
    sub_sub_sub_cancel_right, gammaGaussKernel, gammaGaussWeight] using h

end MasulloRHProof

theorem solution (φ : ℝ → ℂ) (hSmooth : ContDiff ℝ ∞ φ)
    (hCompact : HasCompactSupport φ) (hPositive : tsupport φ ⊆ Ioi 0) (hOne : φ 1 = 0) :
    let spectral : ℝ → ℂ := fun r => mellin φ (Complex.I * r) *
      (((Complex.digamma (1 / 4 + (r : ℂ) * Complex.I / 2)).re - Real.log Real.pi : ℝ) : ℂ)
    let geometric : ℝ → ℂ := fun t =>
      (φ t + φ t⁻¹) * ((Real.sqrt t / (t ^ 2 - 1) : ℝ) : ℂ)
    Integrable spectral ∧ IntegrableOn geometric (Ioi 1) ∧
      (1 / (2 * (Real.pi : ℂ))) * (∫ r : ℝ, spectral r) =
        -(∫ t in Ioi (1 : ℝ), geometric t) := by
  exact MasulloRHProof.digammaArchimedean_eq_realTrace ⟨hSmooth, hCompact, hPositive, hOne⟩

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
