-- Prove2me | solution 1 for GroundTheory.ProfCoh.OpenNormalSubgroup.mem_nhds_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:08.653963+00:00
-- url     : https://prove2.me/submissions/a5867ab8-ba56-44a6-a9ce-c9426a9abb08

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal

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
open Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G]
open GroundTheory.ProfCoh.OpenNormalSubgroup
namespace GroundTheory.ProfCoh.OpenNormalSubgroup
theorem _root_.solution (U : OpenNormalSubgroup G) : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.toOpenSubgroup.isOpen.mem_nhds U.one_mem
end GroundTheory.ProfCoh.OpenNormalSubgroup
