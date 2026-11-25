-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isClosed_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:15:00.478345+00:00
-- url     : https://prove2.me/submissions/5aa5380b-1264-42f1-b0f6-b5528067db88

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution : IsClosed (frobeniusClosure d L σ : Set G) :=
  Subgroup.isClosed_topologicalClosure _
end GroundTheory.LocalField.Abstract
