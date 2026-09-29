-- Prove2me | solution 1 for MeasureTheory.tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bb87dcce-2a25-5ddb-a63a-00a53d9aeb58

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral

set_option autoImplicit false

open MeasureTheory Real Filter Topology FourierTransform Complex

namespace R1Dirichlet

theorem setIntegral_fourierChar_Icc (a t : ℝ) (ha : 0 ≤ a) (ht : t ≠ 0) :
    ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) =
      ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ) := by
  have hle : -a ≤ a := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hc : (-(2 * π * t) * I : ℂ) ≠ 0 := by
    apply mul_ne_zero _ I_ne_zero
    simp only [neg_ne_zero, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, false_or,
      not_or]
    exact ⟨Real.pi_ne_zero, ht⟩
  have hfun : (fun u : ℝ => ((𝐞 (-(t * u)) : Circle) : ℂ)) =
      fun u : ℝ => Complex.exp ((-(2 * π * t) * I) * (u : ℂ)) := by
    funext u
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  have h1 : (-(2 * ↑π * ↑t) * I) * (a : ℂ) = -((2 * π * a * t : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : (-(2 * ↑π * ↑t) * I) * ((-a : ℝ) : ℂ) = ((2 * π * a * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h1, h2]
  set θ : ℝ := 2 * π * a * t with hθ
  have hnum : Complex.exp (-(θ : ℂ) * I) - Complex.exp ((θ : ℂ) * I) =
      -2 * Complex.sin θ * I := by
    rw [show (-(θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I, exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hnum]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  push_cast
  field_simp

theorem setIntegral_fourier_Icc_eq (h : ℝ → ℂ) (hh : Integrable h) (a : ℝ) :
    ∫ u in Set.Icc (-a) a, 𝓕 h u =
      ∫ t, h t * ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) := by
  set g : ℝ → ℂ := (Set.Icc (-a) a).indicator (fun _ => (1 : ℂ)) with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hF : (𝓕 h) = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) h := rfl
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (f := h) (g := g) Real.continuous_fourierChar continuous_inner hh hgi

  have hL : ∫ u, (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) h u) • g u =
      ∫ u in Set.Icc (-a) a, 𝓕 h u := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    rw [hg, ← hF]
    by_cases hu : u ∈ Set.Icc (-a) a
    · simp [Set.indicator_of_mem hu]
    · simp [Set.indicator_of_notMem hu]

  have hR : ∀ t : ℝ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip g t =
      ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) := by
    intro t
    rw [VectorFourier.fourierIntegral, ← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    rw [LinearMap.flip_apply, innerₗ_apply_apply, RCLike.inner_apply, RCLike.conj_to_real,
      mul_comm u t, hg]
    by_cases hu : u ∈ Set.Icc (-a) a
    · simp [Set.indicator_of_mem hu, Circle.smul_def, mul_comm]
    · simp [Set.indicator_of_notMem hu]
  rw [← hL, hflip]
  congr 1
  funext t
  rw [hR t, smul_eq_mul]

theorem setIntegral_fourier_Icc_eq_integral_sin (h : ℝ → ℂ) (hh : Integrable h) (a : ℝ)
    (ha : 0 ≤ a) :
    ∫ u in Set.Icc (-a) a, 𝓕 h u =
      ∫ t, h t * ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ) := by
  rw [setIntegral_fourier_Icc_eq h hh a]
  apply integral_congr_ae
  have h0 : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
    rw [compl_mem_ae_iff]
    exact measure_singleton 0
  filter_upwards [h0] with t ht
  have ht' : t ≠ 0 := ht
  rw [setIntegral_fourierChar_Icc a t ha ht']

theorem integral_fourier_eq (h : ℝ → ℂ) (hh : Integrable h) (hFh : Integrable (𝓕 h))
    (h0 : ContinuousAt h 0) : ∫ u, 𝓕 h u = h 0 := by
  have := hh.fourierInv_fourier_eq hFh h0
  rw [Real.fourierInv_eq] at this
  simpa using this

theorem main (h : ℝ → ℂ) (hh : Integrable h) (hFh : Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
    Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t) atTop
      (𝓝 ((π : ℂ) * h 0)) := by

  have hT : Tendsto (fun a : ℝ => ∫ u in (-a)..a, 𝓕 h u) atTop (𝓝 (h 0)) := by
    rw [← integral_fourier_eq h hh hFh h0]
    exact intervalIntegral_tendsto_integral hFh tendsto_neg_atTop_atBot tendsto_id

  have hT2 : Tendsto (fun a : ℝ => ∫ t, h t * ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ))
      atTop (𝓝 (h 0)) := by
    refine hT.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_fourier_Icc_eq_integral_sin h hh a ha]

  have hsub : Tendsto (fun R : ℝ => R / (2 * π)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hT3 := hT2.comp hsub
  have hT4 : Tendsto (fun R : ℝ => ∫ t, h t * ((Real.sin (R * t) / (π * t) : ℝ) : ℂ))
      atTop (𝓝 (h 0)) := by
    refine hT3.congr ?_
    intro R
    simp only [Function.comp_apply]
    congr 1
    funext t
    congr 3
    field_simp

  have hT5 := hT4.const_mul (π : ℂ)
  refine hT5.congr ?_
  intro R
  rw [← integral_const_mul]
  congr 1
  funext t
  by_cases ht : t = 0
  · subst ht
    simp
  · have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp

end R1Dirichlet

theorem solution
    (h : ℝ → ℂ) (hh : MeasureTheory.Integrable h)
    (hFh : MeasureTheory.Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
    Filter.Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t)
      Filter.atTop (nhds ((Real.pi : ℂ) * h 0)) :=
  R1Dirichlet.main h hh hFh h0

end S_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral
end P2MW
export P2MW.S_MeasureTheory_tendsto_integral_sin_mul_div_mul_of_integrable_fourierIntegral (solution)
