-- Prove2me | solution 1 for LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:23:47.96964+00:00
-- url     : https://prove2.me/submissions/825fb1f8-e07a-48f9-a86d-9f52462bb894

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardSupL2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardSupL2.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
/-- A squared sum of two extended reals, up to the constant `4`. -/
theorem LevyStochCalc.Ito.Picard.sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  have h1 : a + b ≤ 2 * (a ⊔ b) := by
    calc a + b ≤ (a ⊔ b) + (a ⊔ b) := add_le_add le_sup_left le_sup_right
      _ = 2 * (a ⊔ b) := by ring
  have h2 : (a ⊔ b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases max_choice a b with h | h <;> rw [h]
    · exact le_add_right le_rfl
    · exact le_add_left le_rfl
  calc (a + b) ^ 2 ≤ (2 * (a ⊔ b)) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * (a ⊔ b) ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl h2
omit [MeasurableSpace E] in
/-- The drift dominator is square integrable. -/
theorem solution
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n) {T' : ℝ} (hT' : 0 ≤ T')
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ((‖x₀ i‖₊ : ℝ≥0∞)
        + (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  have hfin' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnnorm_norm]
  have hkey := LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le (P := P)
    (f := fun ω s => ‖coeffs.μ s (X s ω) i‖) hμm.norm hT' hfin'
  have hbfin : ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 ∂P
      < ⊤ := lt_of_le_of_lt hkey (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')
  have hbm : Measurable fun ω : Ω =>
      (‖∫ s in Set.Icc (0 : ℝ) T', ‖coeffs.μ s (X s ω) i‖‖₊ : ℝ≥0∞) ^ 2 :=
    (ENNReal.continuous_coe.measurable.comp
      (LevyStochCalc.Ito.Picard.measurable_setIntegral_slice hμm.norm T').nnnorm).pow_const 2
  refine lt_of_le_of_lt (lintegral_mono fun ω => LevyStochCalc.Ito.Picard.sq_add_le_four_mul _ _) ?_
  rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr
    ⟨ENNReal.pow_lt_top ENNReal.coe_lt_top, hbfin⟩)
