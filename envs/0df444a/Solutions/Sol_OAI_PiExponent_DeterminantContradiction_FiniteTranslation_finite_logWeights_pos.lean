-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.finite_logWeights_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:31:47.86888+00:00
-- url     : https://prove2.me/submissions/b4dacca9-fe38-4d07-8d89-92084e6e88bc

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
  change (0 : ℝ) < (Nat.ceil (Real.log (d.q i.val : ℝ)) : ℝ)
  rw [← d.x_log i.val]
  exact lt_of_lt_of_le zero_lt_one (d.x_one_le (i.val + 1))
