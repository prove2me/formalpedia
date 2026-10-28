-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:15:05.546984+00:00
-- url     : https://prove2.me/submissions/25470b7e-b590-47a3-9920-a9f42ec321d0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoPullOut
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_eval_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stepIocMul_zero_eval_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoPullOut.lean; Apache-2.0; locally patched, see formalization/vendor/port.patch; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
theorem LevyStochCalc.Brownian.Ito.stepIocMul_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    ∀ i : Fin (stepIocMul Ω ha hab V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul Ω ha hab V hVb hVm).partition i.castSucc))
      ((stepIocMul Ω ha hab V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  · exact MeasureTheory.stronglyMeasurable_const
  · exact hVa
theorem LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ 0) V) :
    ∀ i : Fin (stepIocMul₀ Ω hb V hVb hVm).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocMul₀ Ω hb V hVb hVm).partition i.castSucc))
      ((stepIocMul₀ Ω hb V hVb hVm).ξ i) := by
  intro i
  fin_cases i
  exact hVa
/-- A bounded weight measurable before a window, times the window's indicator, is progressively
measurable. -/
theorem solution (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M)
    (hVm : Measurable V) (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V) :
    LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω 0 b ω s)
        = fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).eval s ω := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_zero_eval_readable]
    rw [hfun]
    exact (LevyStochCalc.Brownian.Ito.stepIocMul₀ Ω hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt ℱ hab hVb hVm hVa)
  · have hfun : (fun ω s => V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s)
        = fun ω s => (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).eval s ω := by
      funext ω s; rw [LevyStochCalc.Brownian.Ito.stepIocMul_eval_readable]
    rw [hfun]
    exact (LevyStochCalc.Brownian.Ito.stepIocMul Ω ha' hab V hVb hVm).progressivelyMeasurable_eval ℱ
      (LevyStochCalc.Brownian.Ito.stepIocMul_adapt ℱ ha' hab hVb hVm hVa)
