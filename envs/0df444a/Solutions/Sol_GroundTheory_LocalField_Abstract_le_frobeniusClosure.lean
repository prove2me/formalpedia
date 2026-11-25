-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.le_frobeniusClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:17:38.113394+00:00
-- url     : https://prove2.me/submissions/f3af1822-3dc1-4b8a-8536-f24b34770237

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
theorem _root_.solution : L ⊓ d.ker ≤ frobeniusClosure d L σ :=
  le_sup_right.trans (Subgroup.le_topologicalClosure _)
end GroundTheory.LocalField.Abstract
