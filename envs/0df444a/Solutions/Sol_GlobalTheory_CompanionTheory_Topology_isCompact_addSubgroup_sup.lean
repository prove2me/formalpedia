-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Topology.isCompact_addSubgroup_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:36.688384+00:00
-- url     : https://prove2.me/submissions/76994cdd-9340-45ae-806d-12df3fd2c220

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactSupAddSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Topology
namespace GlobalTheory.CompanionTheory.Topology
theorem _root_.solution : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] (A B : AddSubgroup X), IsCompact (A : Set X) → IsCompact (B : Set X) → IsCompact ((A ⊔ B : AddSubgroup X) : Set X) := by
  intro X _ _ _ A B hA hB
  have h : ((A ⊔ B : AddSubgroup X) : Set X) = (A : Set X) + (B : Set X) := by
    ext x
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_add]
  rw [h]
  exact hA.add hB
end GlobalTheory.CompanionTheory.Topology
