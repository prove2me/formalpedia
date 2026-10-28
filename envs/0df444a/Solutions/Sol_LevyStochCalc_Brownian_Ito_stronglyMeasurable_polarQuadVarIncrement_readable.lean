-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:15.263072+00:00
-- url     : https://prove2.me/submissions/adf9551e-7865-470e-9fc9-98b3e4276f1d

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Polarised
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
section Bounds
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ in
/-- The compensated product across a cell is measurable for the σ-algebra at the right
endpoint. -/
theorem solution {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) := by
  have hM₁ := LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁
  have hM₂ := LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂
  have h1b := hM₁.1 b
  have h1a := (hM₁.1 a).mono (ℱ.rightCont.mono hab)
  have h2b := hM₂.1 b
  have h2a := (hM₂.1 a).mono (ℱ.rightCont.mono hab)
  have hcb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume) :=
    (((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont b))
  have hca : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume) :=
    ((((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab))
  exact ((h1b.sub h1a).mul (h2b.sub h2a)).sub (hcb.sub hca)
