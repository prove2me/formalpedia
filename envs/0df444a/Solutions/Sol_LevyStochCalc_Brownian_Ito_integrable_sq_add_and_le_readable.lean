-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integrable_sq_add_and_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:18.168992+00:00
-- url     : https://prove2.me/submissions/4448b033-c481-4ee1-a8a9-8f3d4090492a

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
/-- A sum of two functions with integrable squares has integrable square, with second moment at
most twice the sum of bounds on theirs. -/
theorem solution {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => (A ω) ^ 2) P) (hB : Integrable (fun ω => (B ω) ^ 2) P)
    {a b : ℝ} (hAle : ∫ ω, (A ω) ^ 2 ∂P ≤ a) (hBle : ∫ ω, (B ω) ^ 2 ∂P ≤ b) :
    Integrable (fun ω => (A ω + B ω) ^ 2) P
      ∧ ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ 2 * a + 2 * b := by
  have hdom : Integrable (fun ω => 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2) P :=
    (hA.const_mul 2).add (hB.const_mul 2)
  have hpt : ∀ ω, (A ω + B ω) ^ 2 ≤ 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2 := fun ω => by
    nlinarith [sq_nonneg (A ω - B ω)]
  have hmeas : Measurable fun ω => (A ω + B ω) ^ 2 := (hAm.add hBm).pow_const 2
  have hint : Integrable (fun ω => (A ω + B ω) ^ 2) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ ∫ ω, (2 * (A ω) ^ 2 + 2 * (B ω) ^ 2) ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = 2 * ∫ ω, (A ω) ^ 2 ∂P + 2 * ∫ ω, (B ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_add (hA.const_mul 2) (hB.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * a + 2 * b := by linarith
