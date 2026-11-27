-- Prove2me | solution 1 for GroundTheory.ProfCoh.scd_le_cd_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:55.294344+00:00
-- url     : https://prove2.me/submissions/e5306580-f4c9-4ff7-915e-91fe50ca49b7

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cdp_le_cd
import Theorems.Thm_GroundTheory_ProfCoh_scdp_le_cdp_add_one
import Theorems.Thm_GroundTheory_ProfCoh_scd_le_iff


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
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution : scd G ≤ cd G + 1 :=
  scd_le_iff.2 fun _ hp => (scdp_le_cdp_add_one hp).trans (add_le_add (cdp_le_cd hp) le_rfl)
end GroundTheory.ProfCoh
