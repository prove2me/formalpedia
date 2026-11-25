-- Prove2me | solution 1 for GroundTheory.ProfCoh.nsmul_cohomology_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:39.791952+00:00
-- url     : https://prove2.me/submissions/67efab65-ccfb-447a-b2a8-f361a3ef5cd5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_nsmul_id_apply

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
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] {m : ℕ}
    (hm : ∀ a : A, m • a = 0) (n : ℕ) (x : cohomology A n) : m • x = 0 := by
  have h0 : m • 𝟙 A = 0 := by
    ext a
    exact hm a
  rw [← cohomologyMap_nsmul_id_apply, h0, cohomologyMap_zero]
  rfl
end GroundTheory.ProfCoh
