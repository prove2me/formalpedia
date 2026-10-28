-- Prove2me | solution 1 for LevyStochCalc.Probability.sq_sum_le_card_sq_mul_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:22:31.119934+00:00
-- url     : https://prove2.me/submissions/399514fb-ec31-47ab-8c86-fb97b80c98ff

import Definitions.Def_KLSModular_LevyStochCalc_Probability_DoobContinuous

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {M : ℝ → Ω → ℝ} {T : ℝ}
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
