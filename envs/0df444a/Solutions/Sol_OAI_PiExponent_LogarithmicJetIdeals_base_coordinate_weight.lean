-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.base_coordinate_weight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:47:33.725628+00:00
-- url     : https://prove2.me/submissions/5b9d7bc9-7417-48b0-9f88-40edf90eaae5

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators
theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (MvPowerSeries.X 0) ≠ 0 →
      q 0 ≤ ∑ j, q j * (b j : ℝ) := by
  intro h
  rw [MvPowerSeries.coeff_X] at h
  split_ifs at h with hb
  · subst hb
    simp [Finsupp.single_apply]
  · exact absurd rfl h
