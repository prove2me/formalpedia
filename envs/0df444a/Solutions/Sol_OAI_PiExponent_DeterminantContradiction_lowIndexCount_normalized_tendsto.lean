-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.lowIndexCount_normalized_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:44:53.211369+00:00
-- url     : https://prove2.me/submissions/a8e3bc5c-47a4-4c38-880b-bab283872f21

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_card_normalized_tendsto_volume_toReal
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_region_volume_toReal
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_logWeights_pos
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => (lowIndexCount d H : Real) / H ^ d.m) atTop
      (nhds ((d.base.A : Real) ^ d.m /
        ((d.m.factorial : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    exact OAI.PiExponent.DeterminantContradiction.fixedData_logWeights_pos nu d i
  have hA : 0 < (d.base.A : Real) := lt_trans d.base.theta_pos d.base.theta_lt_A
  have hcount :=
    OAI.PiExponent.DeterminantContradiction.weightedSimplex_card_normalized_tendsto_volume_toReal
      (MatrixArithmetic.logWeights (finiteDenominators d)) (d.base.A : Real) hw hA
  rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume_toReal
    (MatrixArithmetic.logWeights (finiteDenominators d)) (d.base.A : Real) hw hA] at hcount
  simpa [lowIndexCount] using hcount
