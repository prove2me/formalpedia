-- Prove2me | solution 1 for LevyStochCalc.Probability.sq_sum_le_card_sq_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:36.863285+00:00
-- url     : https://prove2.me/submissions/b17f7497-102d-4b6a-b410-e7f9594e8844

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- A square of a finite sum is bounded by the sum of squares, up to the squared cardinality. -/
theorem solution {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := by
  have h1 : ∑ i ∈ s, f i ≤ (s.card : ℝ≥0∞) * s.sup f := by
    calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, s.sup f :=
          Finset.sum_le_sum fun i hi => Finset.le_sup hi
      _ = (s.card : ℝ≥0∞) * s.sup f := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : s.sup f ^ 2 ≤ ∑ i ∈ s, f i ^ 2 := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup s hne f
      rw [hieq]
      exact Finset.single_le_sum (f := fun j => f j ^ 2) (fun _ _ => zero_le) hi
  calc (∑ i ∈ s, f i) ^ 2 ≤ ((s.card : ℝ≥0∞) * s.sup f) ^ 2 := pow_le_pow_left' h1 2
    _ = (s.card : ℝ≥0∞) ^ 2 * s.sup f ^ 2 := by rw [mul_pow]
    _ ≤ (s.card : ℝ≥0∞) ^ 2 * ∑ i ∈ s, f i ^ 2 := mul_le_mul' le_rfl h2
