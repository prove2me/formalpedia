-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:11:38.21104+00:00
-- url     : https://prove2.me/submissions/25263b0f-396d-4b64-a069-ef147c03d9fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_weighted_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators
theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤ Real.exp
      (-nu * (indexWeight d t.1 - rowWeight d r) + H * d.translationError) := by
  obtain ⟨hC, hε, hk, hT, hTw⟩ :=
    OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds d hnu r t
  have h := OAI.PiExponent.DeterminantContradiction.translation_scalar_weighted_bound
    d hnu r t (Real.log (2 * (d.K : ℝ)) + nu) hC hε hk hT hTw
  simpa [AdmissibleParameters.translationError, add_assoc, add_comm, add_left_comm] using h