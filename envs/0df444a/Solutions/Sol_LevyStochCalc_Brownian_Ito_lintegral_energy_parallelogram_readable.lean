-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:03:45.040972+00:00
-- url     : https://prove2.me/submissions/55b2671b-7ae1-4da0-8abc-203f786af0c7

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLinear

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLinear.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
/-- The squared extended norm of a real number is the extended real of its square. -/
theorem LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq (z : ℝ) : (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := by
  rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from (ofReal_norm z).symm,
    ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
section Energy
variable {H₁ H₂ : Ω → ℝ → ℝ}
/-- The energy density of an integrand is measurable in the sample point. -/
theorem LevyStochCalc.Brownian.Ito.measurable_energyDensity (hm : Measurable (Function.uncurry H₁)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
  have hf : Measurable fun p : Ω × ℝ => (‖H₁ p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp hm).coe_nnreal_ennreal).pow_const 2)
  exact hf.lintegral_prod_right'
omit [IsProbabilityMeasure P] in
/-- **The parallelogram law for the energies.** -/
theorem solution (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s) := hm₁.add hm₂
  have hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s) := hm₁.sub hm₂
  have hpt : ∀ a b : ℝ, (‖a + b‖₊ : ℝ≥0∞) ^ 2 + (‖a - b‖₊ : ℝ≥0∞) ^ 2
      = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
    intro a b
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
    rw [LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq,
      LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, h2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hinner : ∀ ω : Ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
        = 2 * (∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    have ha : Measurable fun s => (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hma.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_add_left ha, ← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
      ← lintegral_add_left (h1.const_mul 2)]
    exact lintegral_congr fun s => hpt _ _
  have e1 := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm₁ T
  have e2 := LevyStochCalc.Brownian.Ito.measurable_energyDensity hm₂ T
  have ea := LevyStochCalc.Brownian.Ito.measurable_energyDensity hma T
  rw [← lintegral_add_left ea, ← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  exact lintegral_congr fun ω => hinner ω
