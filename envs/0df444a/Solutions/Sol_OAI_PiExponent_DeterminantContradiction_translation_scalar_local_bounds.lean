-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:24:47.751588+00:00
-- url     : https://prove2.me/submissions/a1355321-3229-42c6-87e0-4ec78e0e7a4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_center
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_choice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_v2_truncation
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    0 ≤ Real.log (2 * (d.K : ℝ)) + nu ∧
    (∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤
        Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * fixedWeights d i)) ∧
    (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ) ∧
    (∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by
  have hc := translation_scalar_local_bounds_v2_center d hnu r
  have ho := translation_scalar_local_bounds_v2_choice d r t
  have ht := translation_scalar_local_bounds_v2_truncation d
  exact ⟨hc.1, hc.2, ho, ht.1, ht.2⟩