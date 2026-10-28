-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:04:06.162522+00:00
-- url     : https://prove2.me/submissions/9f1c4f0a-47c1-492c-8854-5cabbfca4721

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingaleRiemann

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoMartingaleRiemann.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Weight
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
omit [IsProbabilityMeasure P] in
/-- Multiplying an `L²` integrand by a bounded weight keeps it `L²`. -/
theorem solution
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ → ℝ} {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ ω s, |g ω s| ≤ Kg) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  have hgle : ∀ (ω : Ω) (s : ℝ), (‖g ω s‖₊ : ℝ≥0∞) ≤ (Real.toNNReal Kg : ℝ≥0∞) := by
    intro ω s
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal Kg hKg0, coe_nnnorm, Real.norm_eq_abs]
    exact hKg ω s
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact ENNReal.coe_le_coe.mp (hgle ω s)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = (Real.toNNReal Kg : ℝ≥0∞) ^ 2
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        have hne : ((Real.toNNReal Kg : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω =>
          MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (hq T hT)
