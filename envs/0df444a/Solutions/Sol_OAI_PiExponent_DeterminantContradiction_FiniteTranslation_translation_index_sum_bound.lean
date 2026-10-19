-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_index_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:49:44.117521+00:00
-- url     : https://prove2.me/submissions/a764e9c9-c4d0-4626-81ce-60b7c9c44399

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_weighted_simplex_unweighted_sum_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_weight_lower_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    (∑ i : Fin d.m, (t.1.1 i : ℝ)) ≤ H / d.wstar := by
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.weighted_simplex_unweighted_sum_bound
    (MatrixArithmetic.logWeights (finiteDenominators d)) H d.wstar d.wstar_pos
    (by
      intro i
      exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.log_weight_lower_bound d i)
    t.1.1 t.1.2