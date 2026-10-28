-- Prove2me | solution 1 for LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:06:04.442859+00:00
-- url     : https://prove2.me/submissions/8c23b190-3f03-4c90-ab5b-cdbb6dd8faa4

import Definitions.Def_KLSModular_LevyStochCalc_Probability_AbsMoment

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/AbsMoment.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]
/-- On a probability space, `𝔼|f| ≤ √V` for any bound `V` on the second moment `𝔼f²`. -/
theorem solution {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by
  have hsqnn : (0 : ℝ) ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hV0 : 0 ≤ V := hsqnn.trans hV
  have hs0 : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hssq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV0
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · have hVzero : V = 0 := by rw [← hssq, ← hs_eq]; ring
    have h2 : ∫ ω, f ω ^ 2 ∂P = 0 := le_antisymm (hVzero ▸ hV) hsqnn
    have hae : (fun ω => f ω ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hf2).mp h2
    have hzero : ∫ ω, |f ω| ∂P = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with ω hω
      simp [abs_eq_zero.mpr (sq_eq_zero_iff.mp hω)]
    rw [hzero]
    exact hs0
  · have h2s : (0 : ℝ) < 2 * Real.sqrt V := by linarith
    have hsne : Real.sqrt V ≠ 0 := ne_of_gt hs_pos
    have hyoung : ∀ ω : Ω, |f ω| ≤ (f ω ^ 2 + Real.sqrt V ^ 2) / (2 * Real.sqrt V) := by
      intro ω
      rw [le_div_iff₀ h2s]
      nlinarith [sq_nonneg (|f ω| - Real.sqrt V), sq_abs (f ω)]
    calc ∫ ω, |f ω| ∂P
        ≤ ∫ ω, (f ω ^ 2 + Real.sqrt V ^ 2) / (2 * Real.sqrt V) ∂P :=
          integral_mono hf ((hf2.add (integrable_const _)).div_const _) hyoung
      _ = ((∫ ω, f ω ^ 2 ∂P) + Real.sqrt V ^ 2) / (2 * Real.sqrt V) := by
          rw [integral_div, integral_add hf2 (integrable_const _)]
          simp
      _ ≤ (V + V) / (2 * Real.sqrt V) := by rw [hssq]; gcongr
      _ = Real.sqrt V := by
          rw [div_eq_iff (ne_of_gt h2s)]
          have hmul : Real.sqrt V * (2 * Real.sqrt V) = 2 * Real.sqrt V ^ 2 := by ring
          rw [hmul, hssq]
          ring
