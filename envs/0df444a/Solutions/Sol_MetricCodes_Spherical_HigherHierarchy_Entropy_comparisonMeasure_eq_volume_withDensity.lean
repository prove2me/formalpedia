-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Entropy.comparisonMeasure_eq_volume_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:33.55068+00:00
-- url     : https://prove2.me/submissions/5a56c347-c108-46fe-8b5f-008db51199de

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_beta_one_half_eq_two
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Arcsine_map_withDensity_comp

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.Entropy
namespace MetricCodes.Spherical.HigherHierarchy.Entropy
theorem _root_.solution :
    comparisonMeasure = volume.withDensity comparisonLebesgueDensity := by
  let w : ℝ → ℝ≥0∞ := fun t => betaPDF 1 (1 / 2 : ℝ) (4 * t)
  have hw : Measurable w := by
    exact ((measurable_betaPDFReal 1 (1 / 2)).ennreal_ofReal).comp
      (by fun_prop)
  have hscale : volume.map (fun t : ℝ => t / 4) =
      ENNReal.ofReal 4 • (volume : Measure ℝ) := by
    convert Real.map_volume_mul_right
      (show (4 : ℝ)⁻¹ ≠ 0 by norm_num) using 1
    · congr 1
    · norm_num
  have hbeta : betaPDF 1 (1 / 2 : ℝ) =
      w ∘ (fun t : ℝ => t / 4) := by
    funext t
    dsimp [w, Function.comp_apply]
    congr 1
    ring
  have hdensity : (ENNReal.ofReal 4) • w = comparisonLebesgueDensity := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases ht : 0 < t ∧ t < (1 / 4 : ℝ)
    · have ht₀ : 0 < 4 * t := mul_pos (by norm_num) ht.1
      have ht₁ : 4 * t < 1 := by nlinarith [ht.2]
      unfold comparisonLebesgueDensity
      rw [if_pos ht]
      dsimp [w]
      rw [betaPDF_of_pos_lt_one ht₀ ht₁,
        MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_one_half_eq_two]
      have hremaining : 0 < 1 / 4 - t := by linarith [ht.2]
      have hradical : 1 - 4 * t = 4 * (1 / 4 - t) := by ring
      have hsqrt : Real.sqrt (1 - 4 * t) =
          2 * Real.sqrt (1 / 4 - t) := by
        rw [hradical, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      have hpow : (1 - 4 * t) ^ ((1 / 2 : ℝ) - 1) =
          (Real.sqrt (1 - 4 * t))⁻¹ := by
        convert Real.rpow_neg (by linarith [ht₁] : 0 ≤ 1 - 4 * t)
          (1 / 2 : ℝ) using 1 <;> norm_num [Real.sqrt_eq_rpow]
      have hsqrt_ne : Real.sqrt (1 / 4 - t) ≠ 0 :=
        (Real.sqrt_pos.mpr hremaining).ne'
      rw [hpow, hsqrt]
      norm_num
      let v : ℝ≥0∞ := ENNReal.ofReal ((Real.sqrt (1 / 4 - t))⁻¹)
      change (4 : ℝ≥0∞) *
        (ENNReal.ofReal (1 / 2 : ℝ) *
          (v * ENNReal.ofReal (1 / 2 : ℝ))) = v
      calc
        (4 : ℝ≥0∞) *
            (ENNReal.ofReal (1 / 2 : ℝ) *
              (v * ENNReal.ofReal (1 / 2 : ℝ))) =
            (4 * ENNReal.ofReal (1 / 2 : ℝ) *
              ENNReal.ofReal (1 / 2 : ℝ)) * v := by ac_rfl
        _ = _ := by
          have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ℝ≥0∞)⁻¹ := by
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
            norm_num
          rw [hhalf]
          have hcancel : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ = 1 :=
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
          calc
            (2 * 2 : ℝ≥0∞) * 2⁻¹ * 2⁻¹ * v =
                ((2 * 2⁻¹) * (2 * 2⁻¹)) * v := by ac_rfl
            _ = v := by rw [hcancel]; simp
    · have hnot : ¬ (0 < 4 * t ∧ 4 * t < 1) := by
        intro h
        apply ht
        constructor
        · nlinarith [h.1]
        · nlinarith [h.2]
      change ENNReal.ofReal 4 * betaPDF 1 (1 / 2 : ℝ) (4 * t) =
        comparisonLebesgueDensity t
      rw [comparisonLebesgueDensity, if_neg ht, betaPDF, betaPDFReal,
        if_neg hnot]
      simp
  unfold comparisonMeasure betaMeasure
  rw [hbeta,
    MetricCodes.Spherical.HigherHierarchy.Arcsine.map_withDensity_comp
      (by fun_prop) hw,
    hscale, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal 4) hw, hdensity]
end MetricCodes.Spherical.HigherHierarchy.Entropy
