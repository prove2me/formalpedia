-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.lintegral_eval_mul_sq_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:16:47.953656+00:00
-- url     : https://prove2.me/submissions/0d113f59-45b9-4447-9105-41af2bf7a285

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraSimpleIntegrand_F001
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple integrands as integrands of the `L²` Brownian Itô integral

A simple integrand is uniformly bounded in both variables, jointly measurable, square-integrable
on every time window and, when its coefficients are adapted to a filtration, progressively
measurable, so it is an admissible integrand for the `L²` Itô integral in its own right; the two
elementary integrals of adapted simple integrands obey the Itô isometry for their difference at
an intermediate time, and the `L²` Itô integral of a simple integrand agrees almost everywhere
with its elementary integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.solution {T : ℝ} (G : SimplePredictable Ω T)
    {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    intro s ω
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B :=
          ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
  have hpt : ∀ s ω, (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact hbd s ω
  have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ = ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hne) (hq T' hT')
section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end EvalSimple

end LevyStochCalc.Brownian.Ito
