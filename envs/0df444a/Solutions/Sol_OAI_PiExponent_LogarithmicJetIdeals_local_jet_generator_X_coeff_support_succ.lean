-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.local_jet_generator_X_coeff_support_succ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T16:03:15.568988+00:00
-- url     : https://prove2.me/submissions/ddc3dd1a-2b55-4b17-b11d-8be13e1af590

import Mathlib
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators
theorem solution
    {m : ℕ} (b : Fin (m + 1) → ℕ) (i : Fin m) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (MvPowerSeries.X i.succ) ≠ 0 →
      ∀ j : Fin (m + 1), b j = if j = i.succ then 1 else 0 := by
  intro h j
  rw [MvPowerSeries.coeff_X] at h
  split_ifs at h with hb
  · have := congrArg (fun f : Fin (m + 1) →₀ ℕ => f j) hb
    simp only [InterpolationMatrix.exponentVector, Finsupp.equivFunOnFinite_symm_apply_apply] at this
    rw [this, Finsupp.single_apply]
    by_cases hj : j = i.succ
    · simp [hj]
    · simp [hj, Ne.symm hj]
  · exact absurd rfl h
