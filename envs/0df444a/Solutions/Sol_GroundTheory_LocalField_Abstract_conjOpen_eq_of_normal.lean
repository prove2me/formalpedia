-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.conjOpen_eq_of_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:59.177294+00:00
-- url     : https://prove2.me/submissions/b8141627-7b30-4c7c-8c7c-3c48bb3d3900

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoCyclic
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_IsoPGroup
import Theorems.Thm_GroundTheory_LocalField_Abstract_map_conj_eq_of_normal


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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
omit [CompactSpace G]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {K M : OpenSubgroup G} (hMK : M ≤ K)
    [((M : Subgroup G).subgroupOf K).Normal] {g : G} (hg : g ∈ (K : Subgroup G)) :
    conjOpen g M = M := by
  have h := map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg
  apply OpenSubgroup.ext
  intro x
  show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)
  rw [coe_conjOpen, h]
end GroundTheory.LocalField.Abstract
