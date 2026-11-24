-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_generic_exp_infimum_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:05:33.919939+00:00
-- url     : https://prove2.me/submissions/83c8dee6-ff51-4fc0-bca5-148164d1ba5d

import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_weighted_infimum_interval_scale
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_exponential_product_mixture_density
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Separate the weighted CDF computation from translation and Tonelli. -/
theorem solution :
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (φ q : ℝ) (w : ℝ → ℝ), 0 < φ → 0 < q → ν (Iio 0) = 0 →
      (∀ z : ℝ, z < 0 → w z = 0) →
      (∀ z : ℝ, 0 ≤ w z) →
      ContinuousOn w (Ici (0 : ℝ)) →
      (∀ b : ℝ, 0 ≤ b → cdf ν b =
        q / φ * w b - q * ∫ s in (0 : ℝ)..b, w s) →
      ∀ x : ℝ, 0 ≤ x → ∀ A : Set ℝ, MeasurableSet A →
        ((volume.restrict (Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (Real.exp (-φ * y) * w x - w (x - y)))) A =
        (ENNReal.ofReal q)⁻¹ * ((expMeasure φ).prod ν)
          {z : ℝ × ℝ | z.2 ≤ x ∧ x + z.1 - z.2 ∈ A} := by
  intro ν hν φ q w hφ hq hsupp hzero hnonneg hcont hcdf x hx A hA
  rw [withDensity_apply _ hA,
    p2m88_exponential_product_mixture_density ν φ q hφ hq x A hA,
    Measure.restrict_restrict hA]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (hA.inter measurableSet_Ici)] with y hy
  have hy0 : 0 ≤ y := hy.2
  have ha : x - y ≤ x := by linarith
  rw [p2m88_weighted_infimum_interval_scale ν φ q w
    hφ hq hsupp hzero hnonneg hcont hcdf (x - y) x ha,
    ← ENNReal.ofReal_mul (by positivity)]
  have hcoeff : (φ / q) * (q / φ) = 1 := by field_simp
  have h1 : Real.exp (-φ * (y - x)) * Real.exp (-φ * x) =
      Real.exp (-φ * y) := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-φ * (y - x)) * Real.exp (-φ * (x - y)) = 1 := by
    rw [← Real.exp_add, show -φ * (y - x) + -φ * (x - y) = 0 by ring,
      Real.exp_zero]
  congr 1
  symm
  calc
    _ = (φ / q * (q / φ)) *
        ((Real.exp (-φ * (y - x)) * Real.exp (-φ * x)) * w x -
          (Real.exp (-φ * (y - x)) * Real.exp (-φ * (x - y))) * w (x - y)) := by
      ring
    _ = _ := by simp only [hcoeff, h1, h2, one_mul]
