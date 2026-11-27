-- Prove2me | solution 1 for GroundTheory.LocalField.rootEval_eq_rootEval_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:49:49.468271+00:00
-- url     : https://prove2.me/submissions/26316473-a73d-4f61-a55d-9f81410afd34

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LubinTateReciprocity_RootEval
import Theorems.Thm_GroundTheory_LocalField_rootEval_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open PowerSeries
variable {B : Type*} [CommRing B] {I : Ideal B} {P : Polynomial B}
variable [IsAdicComplete I B] (hP : P.IsDistinguishedAt I)
namespace GroundTheory.LocalField
theorem _root_.solution (F G : B⟦X⟧) :
    rootEval hP F = rootEval hP G ↔ F - G ∈ Ideal.span {(P : B⟦X⟧)} := by
  rw [← rootEval_eq_zero_iff hP, map_sub, sub_eq_zero]
end GroundTheory.LocalField
