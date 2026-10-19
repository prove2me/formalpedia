-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:54:39.782302+00:00
-- url     : https://prove2.me/submissions/67710866-638b-42db-9964-adb27b2a14ba

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    d.wstar ≤ MatrixArithmetic.logWeights (finiteDenominators d) i := by
  have h := d.wstar_lower i
  rw [d.x_log i.val] at h
  simpa [MatrixArithmetic.logWeights, finiteDenominators] using h