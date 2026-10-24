-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.fixedData_logWeights_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:47:20.150802+00:00
-- url     : https://prove2.me/submissions/2a4021c3-66b4-4894-b321-813dcbdcb7fa

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution (nu : Real) (d : FixedData nu) (i : Fin d.m) :
    0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
  unfold MatrixArithmetic.logWeights DeterminantContradiction.finiteDenominators
  have hq : 2 <= d.q i.val := (d.approximations i.val).1
  have hlog : 0 < Real.log (d.q i.val) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < d.q i.val by omega)
  exact_mod_cast (Nat.ceil_pos.mpr hlog)