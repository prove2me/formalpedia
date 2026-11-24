-- Prove2me | solution 2 for GlobalTheory.RelIndexOfMap.relIndex_eq_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:48.119751+00:00
-- url     : https://prove2.me/submissions/f02fa6ca-0ed1-45d6-a399-369b2dcd96d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexEqOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelIndexOfMap
namespace GlobalTheory.RelIndexOfMap
theorem _root_.solution {X P : Type} [Group X] [Group P] (φ : X →* P) (A B : Subgroup X)
    (U V : Subgroup P) (hA : A.map φ = U) (hB : ∀ a ∈ A, a ∈ B ↔ φ a ∈ V) :
    B.relIndex A = V.relIndex U := by
  rw [← hA, ← Subgroup.relIndex_comap]
  unfold Subgroup.relIndex
  congr 1
  ext a
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  exact hB a a.2
end GlobalTheory.RelIndexOfMap
