-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.compensator_add_sq_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:23.985982+00:00
-- url     : https://prove2.me/submissions/5b14d0c9-1343-4363-95dc-b1148ea6183c

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_DriftIncrement
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/DriftIncrement.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory
/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem LevyStochCalc.integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u
end
end

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
include hC0 hCH₁ hCH₂ hm₁ hm₂ in
/-- The compensator of the sum expands by the binomial identity. -/
theorem solution {t : ℝ} (ω : Ω) :
    ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
        + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
        + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume := by
  have hfin : volume (Set.Icc (0 : ℝ) t) ≠ ⊤ := (measure_Icc_lt_top).ne
  have hm₁' : Measurable (H₁ ω) := Measurable.of_uncurry_left hm₁
  have hm₂' : Measurable (H₂ ω) := Measurable.of_uncurry_left hm₂
  have hsq : ∀ x : ℝ, |x| ≤ C → x ^ 2 ≤ C ^ 2 := by
    intro x hx
    nlinarith [abs_nonneg x, sq_abs x]
  have hi₁ : IntegrableOn (fun u => (H₁ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hm₁'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₁ ω u)) hfin
  have hi₂ : IntegrableOn (fun u => (H₂ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hm₂'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₂ ω u)) hfin
  have hi₁₂ : IntegrableOn (fun u => 2 * (H₁ ω u * H₂ ω u)) (Set.Icc (0 : ℝ) t) volume := by
    refine LevyStochCalc.integrableOn_of_bounded_of_measurable (B := 2 * C ^ 2)
      ((measurable_const).mul (hm₁'.mul hm₂')) (fun u => ?_) hfin
    change |2 * (H₁ ω u * H₂ ω u)| ≤ 2 * C ^ 2
    have habs : |2 * (H₁ ω u * H₂ ω u)| = 2 * (|H₁ ω u| * |H₂ ω u|) := by
      rw [abs_mul, abs_mul, abs_two]
    rw [habs]
    nlinarith [hCH₁ ω u, hCH₂ ω u, abs_nonneg (H₁ ω u), abs_nonneg (H₂ ω u)]
  have hexp : ∀ u : ℝ, (H₁ ω u + H₂ ω u) ^ 2
      = (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2 := fun u => by ring
  have hcongr : ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = ∫ u in Set.Icc (0 : ℝ) t,
          ((H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2) ∂volume :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => hexp u
  have hiSum : IntegrableOn (fun u => (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u))
      (Set.Icc (0 : ℝ) t) volume := hi₁.add hi₁₂
  rw [hcongr, MeasureTheory.integral_add hiSum hi₂,
    MeasureTheory.integral_add hi₁ hi₁₂, MeasureTheory.integral_const_mul]
