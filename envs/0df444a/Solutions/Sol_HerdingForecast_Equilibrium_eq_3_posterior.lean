-- Prove2me | solution 1 for HerdingForecast.Equilibrium.eq_3_posterior
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:24:09.718149+00:00
-- url     : https://prove2.me/submissions/f42c2c78-8db8-4c2d-9d29-93f598d496fa

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model

open HerdingForecast.Equilibrium MeasureTheory ProbabilityTheory

theorem solution (P : Params) (hP : Standing P) (x y : ℝ) :
    posterior P x y = ProbabilityTheory.gaussianReal (thetaHat P x y) (postVar P).toNNReal := by
  obtain ⟨_, hx, hy, _, _⟩ := hP
  set V : NNReal := (postVar P).toNNReal with hV
  have hVr : (V : ℝ) = (P.τy + P.τx)⁻¹ := by
    rw [hV, postVar, Real.coe_toNNReal _ (by positivity)]
  have hV0 : V ≠ 0 := by
    intro h; have := congrArg (fun t : NNReal => (t : ℝ)) h
    simp only [hVr, NNReal.coe_zero] at this
    have : 0 < (P.τy + P.τx)⁻¹ := by positivity
    linarith
  set W : NNReal := (P.τx⁻¹ + P.τy⁻¹).toNNReal with hW
  have hWr : (W : ℝ) = P.τx⁻¹ + P.τy⁻¹ := by
    rw [hW, Real.coe_toNNReal _ (by positivity)]
  set C : ℝ := gaussianPDFReal 0 W (x - y) with hC
  have hCpos : 0 < C := by
    apply gaussianPDFReal_pos
    intro h; have := congrArg (fun t : NNReal => (t : ℝ)) h
    simp only [hWr, NNReal.coe_zero] at this
    have : 0 < P.τx⁻¹ + P.τy⁻¹ := by positivity
    linarith
  -- pointwise factorization of the likelihood
  have hfac : ∀ θ, likelihood P x y θ = C * gaussianPDFReal (thetaHat P x y) V θ := by
    intro θ
    have h1 : ((P.τx⁻¹).toNNReal : ℝ) = P.τx⁻¹ := Real.coe_toNNReal _ (by positivity)
    have h2 : ((P.τy⁻¹).toNNReal : ℝ) = P.τy⁻¹ := Real.coe_toNNReal _ (by positivity)
    simp only [likelihood, hC, gaussianPDFReal, h1, h2, hVr, hWr, thetaHat]
    have hsq : √(2 * Real.pi * P.τx⁻¹) * √(2 * Real.pi * P.τy⁻¹)
        = √(2 * Real.pi * (P.τx⁻¹ + P.τy⁻¹)) * √(2 * Real.pi * (P.τy + P.τx)⁻¹) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    have hexp : -(x - θ) ^ 2 / (2 * P.τx⁻¹) + -(y - θ) ^ 2 / (2 * P.τy⁻¹)
        = -(x - y - 0) ^ 2 / (2 * (P.τx⁻¹ + P.τy⁻¹)) +
          -(θ - (P.τx / (P.τy + P.τx) * x + P.τy / (P.τy + P.τx) * y)) ^ 2 /
            (2 * (P.τy + P.τx)⁻¹) := by
      field_simp
      ring
    calc (√(2 * Real.pi * P.τx⁻¹))⁻¹ * Real.exp (-(x - θ) ^ 2 / (2 * P.τx⁻¹)) *
          ((√(2 * Real.pi * P.τy⁻¹))⁻¹ * Real.exp (-(y - θ) ^ 2 / (2 * P.τy⁻¹)))
        = (√(2 * Real.pi * P.τx⁻¹) * √(2 * Real.pi * P.τy⁻¹))⁻¹ *
            Real.exp (-(x - θ) ^ 2 / (2 * P.τx⁻¹) + -(y - θ) ^ 2 / (2 * P.τy⁻¹)) := by
          rw [Real.exp_add, mul_inv]; ring
      _ = _ := by
          rw [hsq, hexp, Real.exp_add, mul_inv]; ring
  have hmeas : volume.withDensity (fun θ => ENNReal.ofReal (likelihood P x y θ))
      = ENNReal.ofReal C • gaussianReal (thetaHat P x y) V := by
    rw [gaussianReal_of_var_ne_zero _ hV0, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext θ
    rw [hfac θ, gaussianPDF_def, Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hCpos.le]
  unfold HerdingForecast.Equilibrium.posterior
  rw [hmeas]
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_univ, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
    ENNReal.inv_mul_cancel (by simpa using hCpos) ENNReal.ofReal_ne_top, one_smul]
