-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.row_card_factorization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:19:01.858651+00:00
-- url     : https://prove2.me/submissions/966e2e2e-ea76-4523-9949-7addd7f3edb6

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ) :
    OAI.PiExponent.DeterminantContradiction.actualRowCount d H = d.K *
      (OAI.PiExponent.strictWeightedSimplex
        (OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
          (OAI.PiExponent.MatrixArithmetic.logWeights
            (OAI.PiExponent.DeterminantContradiction.finiteDenominators d))) H).card := by
  unfold actualRowCount Row InterpolationMatrix.Row
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
