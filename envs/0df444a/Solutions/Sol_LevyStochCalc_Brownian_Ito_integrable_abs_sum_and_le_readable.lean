-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_abs_sum_and_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:02.960979+00:00
-- url     : https://prove2.me/submissions/1704dc03-23d3-4ef1-8b18-3b182be1a67a

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
/-- A finite sum of functions with integrable absolute values has integrable absolute value, and
its first absolute moment is at most the sum of theirs. -/
theorem solution {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω|) P) :
    Integrable (fun ω => |∑ i, f i ω|) P
      ∧ ∫ ω, |∑ i, f i ω| ∂P ≤ ∑ i, ∫ ω, |f i ω| ∂P := by
  have hdom : Integrable (fun ω => ∑ i, |f i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => hfi i
  have hpt : ∀ ω, |∑ i, f i ω| ≤ ∑ i, |f i ω| := fun ω => Finset.abs_sum_le_sum_abs _ _
  have hmeas : Measurable fun ω => |∑ i, f i ω| :=
    (Finset.measurable_sum _ fun i _ => hfm i).abs
  have hint : Integrable (fun ω => |∑ i, f i ω|) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i, f i ω| ∂P ≤ ∫ ω, ∑ i, |f i ω| ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = ∑ i, ∫ ω, |f i ω| ∂P := MeasureTheory.integral_finsetSum _ fun i _ => hfi i
