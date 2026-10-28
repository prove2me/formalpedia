-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_sq_lt_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:15.065278+00:00
-- url     : https://prove2.me/submissions/5e863042-8060-4648-9e36-14b4668f4ec5

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoAlgebraSimpleIntegrand.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- The `L²`-mass of a simple integrand over any time window is finite. -/
theorem solution {T : ℝ} (G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T)
    (P : Measure Ω) [IsProbabilityMeasure P] (T' : ℝ) (_hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hpt : ∀ s ω, ((‖G.eval s ω‖₊ : ℝ≥0∞)) ^ 2 ≤ (ENNReal.ofReal B) ^ 2 := by
    intro s ω
    refine pow_le_pow_left' ?_ 2
    have hx : ‖G.eval s ω‖ ≤ B := (Real.norm_eq_abs _).le.trans (hB s ω)
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hx
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
        (ENNReal.ofReal B) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ < ⊤ := by
        rw [lintegral_const, setLIntegral_const, Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top
