-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:14:50.257541+00:00
-- url     : https://prove2.me/submissions/2403f631-812e-478e-9c16-f40e5573360f

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_ge_one_eventually
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_poly_upper_eventually

open Filter
open OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      1 ≤ actualRowCount d H ∧
      (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1) := by
  obtain ⟨C, hC, hUpper⟩ :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_poly_upper_eventually d
  have hLower :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_ge_one_eventually d
  refine ⟨C, hC, ?_⟩
  filter_upwards [hUpper, hLower] with H hHUpper hHLower
  exact ⟨hHLower, hHUpper⟩