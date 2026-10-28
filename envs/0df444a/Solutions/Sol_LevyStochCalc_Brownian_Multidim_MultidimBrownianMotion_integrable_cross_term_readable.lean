-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:14:45.188511+00:00
-- url     : https://prove2.me/submissions/b882c4ee-cfcf-47fb-8001-5d177c93c5a4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CrossOrthogonalityLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CrossOrthogonalityLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {d : ℕ}
section SimpleIntegrands
open LevyStochCalc.Brownian.Ito
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
/-- The square of a Brownian increment over a possibly degenerate interval is integrable. -/
lemma LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_increment_sq (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Integrable (fun ω => (V.W q ω - V.W p ω) ^ 2) P := by
  rcases eq_or_lt_of_le hpq with h | h
  · have hz : (fun ω => (V.W q ω - V.W p ω) ^ 2) = fun _ => (0 : ℝ) := by
      funext ω; rw [← h]; simp
    rw [hz]
    exact integrable_zero Ω ℝ P
  · exact brownian_increment_sq_integrable V hp h
/-- A product of two bounded coefficients and two Brownian increments is integrable. -/
lemma solution (V₁ V₂ : LevyStochCalc.Brownian.BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
    {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
      * (η ω * (V₂.W v ω - V₂.W r ω))) P := by
  have hm1 : Measurable fun ω => V₁.W q ω - V₁.W p ω :=
    (V₁.measurable_eval q).sub (V₁.measurable_eval p)
  have hm2 : Measurable fun ω => V₂.W v ω - V₂.W r ω :=
    (V₂.measurable_eval v).sub (V₂.measurable_eval r)
  have hprod : Integrable (fun ω => (V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) P := by
    have hdom : Integrable (fun ω => 1 / 2 * (V₁.W q ω - V₁.W p ω) ^ 2
        + 1 / 2 * (V₂.W v ω - V₂.W r ω) ^ 2) P :=
      ((LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_increment_sq V₁ hp hpq).const_mul (1 / 2 : ℝ)).add
        ((LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_increment_sq V₂ hr hrv).const_mul (1 / 2 : ℝ))
    refine Integrable.mono' hdom (hm1.mul hm2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (V₁.W q ω - V₁.W p ω), sq_abs (V₂.W v ω - V₂.W r ω),
      sq_nonneg (|V₁.W q ω - V₁.W p ω| - |V₂.W v ω - V₂.W r ω|)]
  have heq : (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω)) * (η ω * (V₂.W v ω - V₂.W r ω)))
      = fun ω => (ξ ω * η ω) * ((V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) := by
    funext ω; ring
  rw [heq]
  refine Integrable.bdd_mul (c := |Mξ| * |Mη|) hprod (hξm.mul hηm).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)
