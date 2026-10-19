-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coordinate_X_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:50:19.044485+00:00
-- url     : https://prove2.me/submissions/28b39406-4dce-4d96-8add-e53e587dc779

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
theorem solution
    {m : ℕ} (q : Fin (m + 1) → ℝ) (a : Fin (m + 1) → ℕ)
    (r : Fin (m + 1)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (MvPowerSeries.X r) ≠ 0 →
    q r ≤ ∑ j, q j * (a j : ℝ) := by
  intro h
  rw [MvPowerSeries.coeff_X] at h
  split_ifs at h with hb
  · have ha : ∀ j, a j = (Finsupp.single r 1 : Fin (m + 1) →₀ ℕ) j := by
      intro j
      rw [← hb]
      simp [InterpolationMatrix.exponentVector]
    have : ∑ j, q j * (a j : ℝ) = q r := by
      simp only [ha, Finsupp.single_apply]
      simp
    rw [this]
  · exact absurd rfl h
