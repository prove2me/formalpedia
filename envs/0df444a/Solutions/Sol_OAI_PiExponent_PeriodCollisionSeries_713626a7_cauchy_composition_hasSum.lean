-- Prove2me | solution 1 for OAI.PiExponent.PeriodCollisionSeries_713626a7.cauchy_composition_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:02:27.98822+00:00
-- url     : https://prove2.me/submissions/f09e2897-d352-47a9-9bf8-a2181388897e

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open Filter Topology
open scoped BigOperators

theorem solution
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (R : ℝ) (hR : 0 < R)
    (center : ℂ) (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell : ℕ) :
    HasSum
      (fun d : ℕ =>
        cauchyPowerSeries
            (fun t : ℂ => (((center + Complex.log (1 + t)) / (R : ℂ)) ^ d))
            0 (1 / 2) ell (fun _ => (1 : ℂ)) *
          cauchyPowerSeries f 0 R d (fun _ => (R : ℂ)))
      (cauchyPowerSeries (fun t : ℂ => f (center + Complex.log (1 + t)))
        0 (1 / 2) ell (fun _ => (1 : ℂ))) := by
  set p := cauchyPowerSeries f 0 R with hpdef
  set b : ℕ → ℂ := fun d => p d (fun _ => (R : ℂ)) with hb
  set u : ℂ → ℂ := fun t => (center + Complex.log (1 + t)) / (R : ℂ) with hu
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  -- power series expansion of f
  let R' : NNReal := ⟨R, hR.le⟩
  have hp : HasFPowerSeriesOnBall f p 0 R' :=
    (hf.differentiableOn).hasFPowerSeriesOnBall (R := R') (by
      change (0 : NNReal) < ⟨R, hR.le⟩; exact_mod_cast hR)
  have hexp : ∀ y : ℂ, ‖y‖ < R → HasSum (fun d => (y / R) ^ d * b d) (f y) := by
    intro y hy
    have hy' : y ∈ Metric.eball (0 : ℂ) R' := by
      rw [mem_eball_zero_iff]
      exact_mod_cast hy
    have := hp.hasSum hy'
    rw [zero_add] at this
    have e : ∀ d, p d (fun _ => y) = (y / R) ^ d * b d := by
      intro d
      have : (fun _ : Fin d => y) = fun _ => (y / R) • (R : ℂ) := by
        funext i; rw [smul_eq_mul]; field_simp
      rw [this, ContinuousMultilinearMap.map_smul_univ]
      simp [hb, Finset.prod_const, smul_eq_mul, div_pow]
    simpa only [e] using this
  -- bound on b
  set A : ℝ := (2 * Real.pi)⁻¹ * ∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap 0 R θ)‖ with hA
  have hbA : ∀ d, ‖b d‖ ≤ A := by
    intro d
    have h1 := norm_cauchyPowerSeries_le f 0 R d
    have h2 := (p d).le_opNorm (fun _ => (R : ℂ))
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] at h2
    rw [abs_of_pos hR] at h1
    calc ‖b d‖ ≤ ‖p d‖ * R ^ d := h2
      _ ≤ (A * R⁻¹ ^ d) * R ^ d := by gcongr
      _ = A := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow, mul_one]
  -- points on the circle
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 (1 / 2) θ‖ = 1 / 2 := by
    intro θ; rw [norm_circleMap_zero]; norm_num
  have hlog : ∀ θ : ℝ, ‖center + Complex.log (1 + circleMap 0 (1 / 2) θ)‖ ≤ R / 2 := by
    intro θ
    have := Complex.norm_log_one_add_half_le_self (z := circleMap 0 (1 / 2) θ) (by rw [hcirc])
    rw [hcirc] at this
    calc _ ≤ ‖center‖ + ‖Complex.log (1 + circleMap 0 (1 / 2) θ)‖ := norm_add_le _ _
      _ ≤ ‖center‖ + 3 / 4 := by linarith
      _ ≤ R / 2 := hc
  have hu_le : ∀ θ : ℝ, ‖u (circleMap 0 (1 / 2) θ)‖ ≤ 1 / 2 := by
    intro θ
    simp only [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [div_le_iff₀ hR]; linarith [hlog θ]
  rw [cauchyPowerSeries_apply]
  simp_rw [cauchyPowerSeries_apply]
  simp only [circleIntegral, smul_eq_mul, sub_zero]
  simp_rw [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), ← intervalIntegral.integral_mul_const]
  apply HasSum.mul_left
  set K : ℝ → ℂ := fun θ => deriv (circleMap 0 (1 / 2)) θ *
    ((1 / circleMap 0 (1 / 2) θ) ^ ell * (circleMap 0 (1 / 2) θ)⁻¹) with hK
  have hKn : ∀ θ, ‖K θ‖ = 2 ^ ell := by
    intro θ
    have h0 : circleMap 0 (1 / 2) θ ≠ 0 := by
      intro h; have := hcirc θ; rw [h] at this; norm_num at this
    simp only [hK, deriv_circleMap, norm_mul, norm_pow, norm_div, norm_inv, hcirc,
      Complex.norm_I, norm_one]
    norm_num
    ring
  have hmeas_u : Measurable fun θ : ℝ => u (circleMap 0 (1 / 2) θ) := by
    simp only [hu]
    exact ((measurable_const.add (Complex.measurable_log.comp
      (measurable_const.add (continuous_circleMap 0 _).measurable))).div_const _)
  have hmeas_K : Measurable K := by
    simp only [hK, deriv_circleMap]
    exact (((continuous_circleMap 0 _).mul continuous_const).measurable).mul
      ((((continuous_circleMap 0 _).measurable.const_div 1).pow_const _).mul
        (continuous_circleMap 0 _).measurable.inv)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun d _ => 2 ^ ell * A * (1 / 2) ^ d) ?_ ?_ ?_ ?_ ?_
  · intro d
    apply Measurable.aestronglyMeasurable
    have : (fun θ => deriv (circleMap 0 (1 / 2)) θ * ((1 / circleMap 0 (1 / 2) θ) ^ ell *
        ((circleMap 0 (1 / 2) θ)⁻¹ * ((center + Complex.log (1 + circleMap 0 (1 / 2) θ)) / ↑R) ^ d))
        * b d) = fun θ => K θ * u (circleMap 0 (1 / 2) θ) ^ d * b d := by
      funext θ; simp only [hK, hu]; ring
    rw [this]
    exact ((hmeas_K.mul (hmeas_u.pow_const d)).mul_const _)
  · intro d
    refine Filter.Eventually.of_forall fun θ _ => ?_
    have : deriv (circleMap 0 (1 / 2)) θ * ((1 / circleMap 0 (1 / 2) θ) ^ ell *
        ((circleMap 0 (1 / 2) θ)⁻¹ * ((center + Complex.log (1 + circleMap 0 (1 / 2) θ)) / ↑R) ^ d))
        * b d = K θ * u (circleMap 0 (1 / 2) θ) ^ d * b d := by
      simp only [hK, hu]; ring
    rw [this, norm_mul, norm_mul, hKn, norm_pow]
    have := hbA d
    have h2 := hu_le θ
    have : ‖u (circleMap 0 (1 / 2) θ)‖ ^ d ≤ (1 / 2) ^ d := by gcongr
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hbA 0)
    calc 2 ^ ell * ‖u (circleMap 0 (1 / 2) θ)‖ ^ d * ‖b d‖ ≤ 2 ^ ell * (1 / 2) ^ d * A := by
          gcongr
      _ = _ := by ring
  · exact Filter.Eventually.of_forall fun θ _ =>
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have hy : ‖center + Complex.log (1 + circleMap 0 (1 / 2) θ)‖ < R := by
      linarith [hlog θ]
    have := (hexp _ hy).mul_left (K θ)
    have e1 : (fun d => deriv (circleMap 0 (1 / 2)) θ * ((1 / circleMap 0 (1 / 2) θ) ^ ell *
        ((circleMap 0 (1 / 2) θ)⁻¹ * ((center + Complex.log (1 + circleMap 0 (1 / 2) θ)) / ↑R) ^ d))
        * b d) = fun d => K θ * (((center + Complex.log (1 + circleMap 0 (1 / 2) θ)) / ↑R) ^ d * b d) := by
      funext d; simp only [hK]; ring
    have e2 : deriv (circleMap 0 (1 / 2)) θ * ((1 / circleMap 0 (1 / 2) θ) ^ ell *
        ((circleMap 0 (1 / 2) θ)⁻¹ * f (center + Complex.log (1 + circleMap 0 (1 / 2) θ)))) =
        K θ * f (center + Complex.log (1 + circleMap 0 (1 / 2) θ)) := by
      simp only [hK]; ring
    rw [e1, e2]; exact this
