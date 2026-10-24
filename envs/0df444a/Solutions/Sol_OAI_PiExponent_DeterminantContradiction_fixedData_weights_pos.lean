-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.fixedData_weights_pos
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:24:54.305415+00:00
-- url     : https://prove2.me/submissions/e31bea93-9a04-4b43-85d6-7a2a5542b849

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution (nu : Real) (d : FixedData nu) :
    0 < (d.w0 : Real) ∧
      ∀ i : Fin d.m,
        0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
  refine ⟨d.w0_pos, ?_⟩
  intro i
  have hq : (1 : Real) < (d.q i.val : Real) := by
    exact_mod_cast
      (lt_of_lt_of_le (show 1 < 2 by decide) (d.approximations i.val).1)
  have hlog : 0 < Real.log (d.q i.val : Real) := Real.log_pos hq
  change 0 < (↑(Nat.ceil (Real.log (d.q i.val : Real))) : Real)
  exact_mod_cast (Nat.ceil_pos.mpr hlog)