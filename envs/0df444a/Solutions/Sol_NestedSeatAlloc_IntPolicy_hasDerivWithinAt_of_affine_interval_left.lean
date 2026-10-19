-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.hasDerivWithinAt_of_affine_interval_left
-- status  : ACCEPTED   (disprove)
-- author  : @vebis
-- created : 2026-10-19T12:23:30.740433+00:00
-- url     : https://prove2.me/submissions/d740fb1e-a1ce-420f-a31a-1ad3db50e931

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {g : ℝ → ℝ} {m : ℕ} {c d s : ℝ}
    (hs : s ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ))
    (haff : ∀ t ∈ Set.Icc ((m : ℝ) - 1) (m : ℝ), g t = c + d * t),
    HasDerivWithinAt g d (Set.Iic s) s) := by
  intro H
  let g : ℝ → ℝ := fun t => if 0 ≤ t then 0 else 1
  have hs : (0:ℝ) ∈ Set.Icc (((1:ℕ) : ℝ) - 1) ((1:ℕ) : ℝ) := by
    simp
  have haff : ∀ t ∈ Set.Icc (((1:ℕ) : ℝ) - 1) ((1:ℕ) : ℝ), g t = (0:ℝ) + 0 * t := by
    intro t ht
    have : 0 ≤ t := by simpa using ht.1
    simp [g, this]
  have h := H (g := g) (m := 1) (c := 0) (d := 0) (s := 0) hs haff
  have hc : ContinuousWithinAt g (Set.Iic 0) 0 := h.continuousWithinAt
  have h1 : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds (g 0)) :=
    hc.tendsto.mono_left (nhdsWithin_mono _ Set.Iio_subset_Iic_self)
  have h2 : Filter.Tendsto g (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : ¬ (0 ≤ t) := not_le.mpr ht
    simp [g, this]
  have := tendsto_nhds_unique h1 h2
  simp [g] at this
