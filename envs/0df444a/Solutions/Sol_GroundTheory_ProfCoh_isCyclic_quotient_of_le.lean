-- Prove2me | solution 1 for GroundTheory.ProfCoh.isCyclic_quotient_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:39.721066+00:00
-- url     : https://prove2.me/submissions/bef73ee1-cacb-4503-8a2f-1e9ef2cca1bb

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {M N : Subgroup G} [M.Normal] [N.Normal] (h : M ≤ N)
    [IsCyclic (G ⧸ M)] : IsCyclic (G ⧸ N) :=
  isCyclic_of_surjective (QuotientGroup.map M N (MonoidHom.id G) h) fun y ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩
end GroundTheory.ProfCoh
