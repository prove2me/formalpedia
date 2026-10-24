-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:35:13.545029+00:00
-- url     : https://prove2.me/submissions/5d51c68b-1425-4d51-a2fc-b81500504eac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_center_log_prefactor
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_center_multiplier_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) := by
  constructor
  · exact OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center_log_prefactor d hnu
  · intro i
    exact OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_v2_center_multiplier_bound
      d hnu i r.1.val (Nat.le_of_lt r.1.isLt)