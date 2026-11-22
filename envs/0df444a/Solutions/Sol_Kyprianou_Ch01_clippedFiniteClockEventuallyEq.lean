-- Prove2me | solution 1 for Kyprianou.Ch01.clippedFiniteClockEventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:57:38.594322+00:00
-- url     : https://prove2.me/submissions/ee721e4d-7691-4096-af8e-0a241d9b1166

import Mathlib
open Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Finite times are eventually unchanged by integer horizon clipping. -/
theorem solution (t : ℝ≥0) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (min (t : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0)).untopD
        (n : ℝ≥0) = t := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have hNt : t ≤ (N : ℝ≥0) := by
    exact_mod_cast hN.le
  filter_upwards [eventually_ge_atTop N] with n hn
  have htn : t ≤ (n : ℝ≥0) :=
    le_trans hNt (by exact_mod_cast hn)
  have hle : (t : WithTop ℝ≥0) ≤
      ((n : ℝ≥0) : WithTop ℝ≥0) :=
    WithTop.coe_le_coe.mpr htn
  rw [min_eq_left hle, WithTop.untopD_coe]
