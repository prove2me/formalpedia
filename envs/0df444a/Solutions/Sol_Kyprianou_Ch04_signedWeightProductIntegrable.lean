-- Prove2me | solution 1 for Kyprianou.Ch04.signedWeightProductIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:00:03.850895+00:00
-- url     : https://prove2.me/submissions/b632f039-080e-46f8-a65c-c1afa2a1aafc

import Mathlib
open MeasureTheory
set_option autoImplicit false
universe u

/-- Weighted square integrability controls the corresponding weighted cross product. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W A B : Ω → ℝ)
    (hW : AEStronglyMeasurable W P) (hAm : AEStronglyMeasurable A P)
    (hBm : AEStronglyMeasurable B P)
    (hA : Integrable (fun ω => W ω * (A ω)^2) P)
    (hB : Integrable (fun ω => W ω * (B ω)^2) P) :
    Integrable (fun ω => W ω * A ω * B ω) P := by
  have hdom : Integrable (fun ω => ‖W ω * (A ω)^2‖ + ‖W ω * (B ω)^2‖) P :=
    hA.norm.add hB.norm
  apply hdom.mono' ((hW.mul hAm).mul hBm)
  filter_upwards [] with ω
  change ‖W ω * A ω * B ω‖ ≤ ‖W ω * (A ω)^2‖ + ‖W ω * (B ω)^2‖
  simp only [Real.norm_eq_abs, abs_mul, abs_pow]
  have h : |A ω| * |B ω| ≤ |A ω|^2 + |B ω|^2 := by
    nlinarith [sq_nonneg (|A ω| - |B ω|), sq_nonneg |A ω|, sq_nonneg |B ω|]
  calc
    |W ω| * |A ω| * |B ω| = |W ω| * (|A ω| * |B ω|) := by ring
    _ ≤ |W ω| * (|A ω|^2 + |B ω|^2) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = |W ω| * |A ω|^2 + |W ω| * |B ω|^2 := by ring
