-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:34.71974+00:00
-- url     : https://prove2.me/submissions/1d14b6ca-efad-4b53-b617-5755b0c31d0c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cochainsMap_add

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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (f g : A ⟶ B)
    (n : ℕ) : cohomologyMap (f + g) n = cohomologyMap f n + cohomologyMap g n := by
  rw [cohomologyMap, cochainsMap_add]
  exact HomologicalComplex.homologyMap_add _ _ _
end GroundTheory.ProfCoh
