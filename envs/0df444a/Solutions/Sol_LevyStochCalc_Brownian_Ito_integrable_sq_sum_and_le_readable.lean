-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_sq_sum_and_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:19.303033+00:00
-- url     : https://prove2.me/submissions/53b9e882-4faa-4d1e-bfdf-c55420c9f6e6

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcess

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcess.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section FiniteSums
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {ι : Type*} [Fintype ι]
/-- A finite sum of functions with integrable squares has integrable square, and its second
moment is at most the number of summands times the sum of theirs. -/
theorem solution {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => (f i ω) ^ 2) P) :
    Integrable (fun ω => (∑ i, f i ω) ^ 2) P
      ∧ ∫ ω, (∑ i, f i ω) ^ 2 ∂P
        ≤ (Fintype.card ι : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂P := by
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2) P :=
    (MeasureTheory.integrable_finsetSum _ fun i _ => hfi i).const_mul _
  have hpt : ∀ ω, (∑ i, f i ω) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2 := fun ω => by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => f i ω)
    simpa using h
  have hmeas : Measurable fun ω => (∑ i, f i ω) ^ 2 :=
    (Finset.measurable_sum _ fun i _ => hfm i).pow_const 2
  have hint : Integrable (fun ω => (∑ i, f i ω) ^ 2) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, (∑ i, f i ω) ^ 2 ∂P
      ≤ ∫ ω, (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (Fintype.card ι : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun i _ => hfi i]
