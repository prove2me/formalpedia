-- Prove2me | solution 1 for Kyprianou.Ch02.truncatedCumulativeAtomicSeriesAgreementV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:30:20.573603+00:00
-- url     : https://prove2.me/submissions/b20c78e9-138c-4fd9-b53d-e6d758cc75c8

import Mathlib
open MeasureTheory Set Function Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Truncated atomic marks recover every smaller cumulative sum. -/
theorem solution
    (g : ℝ≥0 → ℝ) (B : ℝ≥0)
    (hs : Summable (fun s : Ioc (0 : ℝ≥0) B => |g s|)) :
    Summable (fun u : ℝ≥0 => |(Ioc (0 : ℝ≥0) B).indicator g u|) ∧
      ∀ s : ℝ≥0, s ≤ B →
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          (Ioc (0 : ℝ≥0) B).indicator g u else 0) =
          ∑' u : Ioc (0 : ℝ≥0) s, g u := by
  classical
  constructor
  · have h : Summable ((Ioc (0 : ℝ≥0) B).indicator (fun u => |g u|)) :=
      (summable_subtype_iff_indicator (f := fun u : ℝ≥0 => |g u|)
        (s := Ioc 0 B)).mp hs
    apply h.congr
    intro u
    by_cases hu : u ∈ Ioc (0 : ℝ≥0) B <;> simp [hu]
  · intro s hsB
    rw [tsum_subtype (Ioc (0 : ℝ≥0) s) g]
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u ≤ s
    · have huB : u ∈ Ioc (0 : ℝ≥0) B := ⟨hu.1, hu.2.trans hsB⟩
      have hus : u ∈ Ioc (0 : ℝ≥0) s := hu
      rw [if_pos hu, Set.indicator_of_mem huB, Set.indicator_of_mem hus]
    · have hus : u ∉ Ioc (0 : ℝ≥0) s := hu
      rw [if_neg hu, Set.indicator_of_notMem hus]
