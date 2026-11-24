-- Prove2me | solution 1 for GlobalTheory.T.isCompact_sup_addSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:12.314814+00:00
-- url     : https://prove2.me/submissions/86d8115f-e496-4a67-b2f8-d5f671163915

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroupStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Topology_isCompact_addSubgroup_sup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  first | exact @GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | exact GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup | (intros; apply GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup <;> assumption)
end _root_.GlobalTheory.T
