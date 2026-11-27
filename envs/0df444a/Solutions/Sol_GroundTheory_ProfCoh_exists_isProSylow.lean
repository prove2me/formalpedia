-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_isProSylow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:56.691871+00:00
-- url     : https://prove2.me/submissions/2725a951-a545-46c8-bf3e-b94255ab6178

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Definitions.Def_GroundTheory_ProfiniteCohomology_OfNatRelIndexSupAntitone
import Definitions.Def_GroundTheory_ProfiniteCohomology_IsProPGroupSubgroupIffIsPGroupMap
import Definitions.Def_GroundTheory_ProfiniteCohomology_NotDvdSuperIndexIffMap
import Theorems.Thm_GroundTheory_ProfCoh_exists_isProSylow_le
import Theorems.Thm_GroundTheory_ProfCoh_isProPGroup_bot


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
open Pointwise CategoryTheory
variable {G : Type*} [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
variable {p : ℕ} [hp : Fact p.Prime]
namespace GroundTheory.ProfCoh
theorem _root_.solution : ∃ P : Subgroup G, IsProSylow p P :=
  let ⟨P, hP, _⟩ := exists_isProSylow_le (isProPGroup_bot (G := G) p)
  ⟨P, hP⟩
end GroundTheory.ProfCoh
