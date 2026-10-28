-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:40.536911+00:00
-- url     : https://prove2.me/submissions/fef95170-a5d7-4f5c-83fe-8ada5f80d2d1

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
/-- Scaling an integrand scales its energy by the square of the scalar. -/
theorem solution {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (c T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ENNReal.ofReal (c ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hpt : ∀ a : ℝ, (‖c * a‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal (c ^ 2) * (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro a
    rw [LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq, LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  have hinner : ∀ ω : Ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, (‖c * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = ENNReal.ofReal (c ^ 2)
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have h1 : Measurable fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2 :=
      (((measurable_nnnorm.comp (hm.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
    rw [← lintegral_const_mul _ h1]
    exact lintegral_congr fun s => hpt _
  rw [← lintegral_const_mul _ (LevyStochCalc.Brownian.Ito.measurable_energyDensity hm T)]
  exact lintegral_congr fun ω => hinner ω
