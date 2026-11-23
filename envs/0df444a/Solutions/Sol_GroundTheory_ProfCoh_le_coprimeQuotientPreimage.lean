-- Prove2me | solution 1 for GroundTheory.ProfCoh.le_coprimeQuotientPreimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:53.502837+00:00
-- url     : https://prove2.me/submissions/831f8872-1d43-403e-93e9-3a97466a0377

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
variable (N : Subgroup G) [N.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution (p : ℕ) : N ≤ coprimeQuotientPreimage N p := by
  intro x hx
  rw [coprimeQuotientPreimage, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _
end GroundTheory.ProfCoh
