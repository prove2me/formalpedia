-- Prove2me | solution 1 for GroundTheory.ProfCoh.primarySubmodule_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:51.557821+00:00
-- url     : https://prove2.me/submissions/bafc30ef-b2e8-451b-8e43-c394cbce062c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite

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
variable {k : Type u} [CommRing k]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G) (p : ℕ) (g : G) :
    primarySubmodule A p ≤ (primarySubmodule A p).comap (A.ρ g) :=
  fun a ⟨k, hk⟩ => ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
end GroundTheory.ProfCoh
