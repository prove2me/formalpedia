-- Prove2me | solution 1 for Kyprianou.Ch01.measurableDyadicCeilingRandomEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:49:56.623807+00:00
-- url     : https://prove2.me/submissions/fbab7bf3-a91f-4fe1-93b8-198058d72558

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The evaluation of a measurable path family at a random dyadic-grid
time is measurable without any sample-path regularity assumption. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (F t))
    (T : Ω → ℝ≥0) (hT : Measurable T) (n : ℕ) :
    Measurable (fun ω : Ω =>
      F ((⌈T ω * (2 : ℝ≥0) ^ n⌉₊ : ℝ≥0) /
        (2 : ℝ≥0) ^ n) ω) := by
  have hPath : Measurable (fun ω : Ω => fun s : ℝ≥0 => F s ω) :=
    measurable_pi_iff.2 hMeas
  have hGrid : Measurable (fun p : (ℝ≥0 → ℝ) × ℕ =>
      p.1 ((p.2 : ℝ≥0) / (2 : ℝ≥0) ^ n)) :=
    measurable_from_prod_countable_left
      (fun k => measurable_pi_apply ((k : ℝ≥0) / (2 : ℝ≥0) ^ n))
  have hIndex : Measurable (fun ω : Ω => ⌈T ω * (2 : ℝ≥0) ^ n⌉₊) :=
    Nat.measurable_ceil.comp (hT.mul_const _)
  exact hGrid.comp (hPath.prodMk hIndex)
