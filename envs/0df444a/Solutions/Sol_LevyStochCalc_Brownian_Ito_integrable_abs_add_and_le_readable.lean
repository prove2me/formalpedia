-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_abs_add_and_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:54.514258+00:00
-- url     : https://prove2.me/submissions/47a59d65-afbd-45a4-9a8d-8d19cb68faca

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
/-- A sum of two functions with integrable absolute values has integrable absolute value, with
first absolute moment at most the sum of bounds on theirs. -/
theorem solution {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => |A ω|) P) (hB : Integrable (fun ω => |B ω|) P)
    {a b : ℝ} (hAle : ∫ ω, |A ω| ∂P ≤ a) (hBle : ∫ ω, |B ω| ∂P ≤ b) :
    Integrable (fun ω => |A ω + B ω|) P ∧ ∫ ω, |A ω + B ω| ∂P ≤ a + b := by
  have hdom : Integrable (fun ω => |A ω| + |B ω|) P := hA.add hB
  have hpt : ∀ ω, |A ω + B ω| ≤ |A ω| + |B ω| := fun ω => abs_add_le _ _
  have hmeas : Measurable fun ω => |A ω + B ω| := (hAm.add hBm).abs
  have hint : Integrable (fun ω => |A ω + B ω|) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |A ω + B ω| ∂P ≤ ∫ ω, (|A ω| + |B ω|) ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (∫ ω, |A ω| ∂P) + ∫ ω, |B ω| ∂P := MeasureTheory.integral_add hA hB
    _ ≤ a + b := add_le_add hAle hBle
