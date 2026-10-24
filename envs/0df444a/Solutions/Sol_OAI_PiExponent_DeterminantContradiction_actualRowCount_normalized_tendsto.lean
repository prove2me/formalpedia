-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_normalized_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:30:48.854555+00:00
-- url     : https://prove2.me/submissions/43759c5a-ecb3-4a92-9211-680691f9713c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_rowWeights_pos
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_normalized_tendsto_of_weightedSimplex_corrected

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => (actualRowCount d H : Real) / H ^ (d.m + 1)) atTop
      (nhds ((d.K : Real) * (d.base.theta : Real) ^ d.m /
        (((d.m + 1).factorial : Real) * (d.v0 : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by
  apply actualRowCount_normalized_tendsto_of_weightedSimplex_corrected nu d
  apply weightedSimplex_card_normalized_tendsto
  exact fixedData_rowWeights_pos nu d