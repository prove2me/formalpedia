-- Prove2me | solution 1 for GlobalTheory.Published.realMetaplecticRepresentation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:07.130378+00:00
-- url     : https://prove2.me/submissions/449067a7-7572-4687-99a5-c4a50dbb79dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_RealMetaplecticRepresentationHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealMetaplecticRepresentationHolds
import Theorems.Thm_CompanionTheory_ThKR_realMetaplecticRepresentation_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace GlobalTheory.Published
theorem _root_.solution : GlobalTheory.Published.RealMetaplecticRepresentation :=
  CompanionTheory.ThKR.realMetaplecticRepresentation_holds
end GlobalTheory.Published
