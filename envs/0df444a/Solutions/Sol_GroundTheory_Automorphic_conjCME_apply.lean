-- Prove2me | solution 1 for GroundTheory.Automorphic.conjCME_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:34:17.920633+00:00
-- url     : https://prove2.me/submissions/8d53b622-553d-471e-baca-409fc08de2b8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution (k x : G) : conjCME k x = k * x * k⁻¹ := rfl
end GroundTheory.Automorphic
