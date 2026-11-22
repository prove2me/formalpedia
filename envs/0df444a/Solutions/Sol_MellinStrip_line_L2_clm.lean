-- Prove2me | solution 1 for MellinStrip.line_L2_clm
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T07:00:28.017983+00:00
-- url     : https://prove2.me/submissions/8ef0a9be-33ce-4dab-870a-2b273e9156e7

import Mathlib

set_option autoImplicit false

open MeasureTheory

theorem solution (a : ℝ) (N : ℕ) :
    ∃ L : SchwartzMap ℝ ℂ →L[ℂ] Lp ℂ 2 (volume : Measure ℝ), ∀ g : SchwartzMap ℝ ℂ,
      (L g : ℝ → ℂ) =ᵐ[volume] fun y : ℝ =>
        ((a : ℂ) + y * Complex.I) ^ N * ∫ x : ℝ, g x * Complex.exp (y * Complex.I * x) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  let A : ℝ →L[ℝ] ℝ := (-(2 * Real.pi)⁻¹) • ContinuousLinearMap.id ℝ ℝ
  have hA : ∀ x, A x = -(2 * Real.pi)⁻¹ * x := fun x => by simp [A]
  have hg : (A : ℝ → ℝ).HasTemperateGrowth := A.hasTemperateGrowth
  have hup : ∃ (k : ℕ) (C : ℝ), ∀ x : ℝ, ‖x‖ ≤ C * (1 + ‖A x‖) ^ k := by
    refine ⟨1, 2 * Real.pi, fun x => ?_⟩
    rw [hA, pow_one, norm_mul, norm_neg, norm_inv, Real.norm_of_nonneg hpi.le, mul_add, mul_one,
      ← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul]
    linarith [norm_nonneg x, hpi]
  have hofR : (fun y : ℝ => (y : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth
  have hp : (fun y : ℝ => ((a : ℂ) + y * Complex.I) ^ N).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const (a : ℂ)).add
      (hofR.mul (Function.HasTemperateGrowth.const Complex.I))).pow N
  refine ⟨(SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => ((a : ℂ) + y * Complex.I) ^ N)).comp
      ((SchwartzMap.compCLM ℂ hg hup).comp (SchwartzMap.fourierTransformCLM ℂ))), fun g => ?_⟩
  refine (SchwartzMap.coeFn_toLp _ 2 volume).trans (Filter.Eventually.of_forall fun y => ?_)
  change (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => ((a : ℂ) + y * Complex.I) ^ N)
    (SchwartzMap.compCLM ℂ hg hup (SchwartzMap.fourierTransformCLM ℂ g))) y = _
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, SchwartzMap.compCLM_apply, smul_eq_mul,
    Function.comp_apply, SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm, hA]
  congr 2
  push_cast
  field_simp
