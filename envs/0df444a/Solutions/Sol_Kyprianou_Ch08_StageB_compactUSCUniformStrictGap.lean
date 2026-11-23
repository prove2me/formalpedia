-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.compactUSCUniformStrictGap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:44:20.831856+00:00
-- url     : https://prove2.me/submissions/60dd9545-e790-42b4-a6de-36c8f1168ef4

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (f : ℝ≥0 → ℝ) (a : ℝ≥0) (h : ℝ)
    (hUSC : UpperSemicontinuousOn f (Set.Icc 0 a))
    (hStrict : ∀ t : ℝ≥0, t ≤ a → f t < h) :
    ∃ n : ℕ, ∀ t : ℝ≥0, t ≤ a →
      f t < h - 1 / (((n + 1 : ℕ) : ℝ)) := by
  have hNonempty : (Set.Icc (0 : ℝ≥0) a).Nonempty :=
    ⟨0, le_rfl, bot_le⟩
  obtain ⟨u, hu, hmax⟩ :=
    UpperSemicontinuousOn.exists_isMaxOn
      hNonempty isCompact_Icc hUSC
  have hfu : f u < h := hStrict u hu.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hfu)
  refine ⟨n, ?_⟩
  intro t ht
  have hle : f t ≤ f u := hmax ⟨bot_le, ht⟩
  have hgap : (1 : ℝ) / (((n + 1 : ℕ) : ℝ)) < h - f u := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  linarith
