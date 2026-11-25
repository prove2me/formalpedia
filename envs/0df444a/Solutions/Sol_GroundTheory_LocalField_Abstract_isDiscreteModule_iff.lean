-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.isDiscreteModule_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:49.28264+00:00
-- url     : https://prove2.me/submissions/4f818cca-1af3-4dd0-8a33-b3b6f7a16bb7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule

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
variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution [ContinuousMul G] :
    IsDiscreteModule G A ↔ ∀ a : A, ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) := by
  constructor
  · intro h a
    exact ⟨⟨MulAction.stabilizer G a, h.isOpen_stabilizer a⟩, fun g hg => hg⟩
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨U, hU⟩ := h a
    exact Subgroup.isOpen_mono (H₁ := (U : Subgroup G)) (fun g hg => hU g hg) U.isOpen
end GroundTheory.LocalField.Abstract
