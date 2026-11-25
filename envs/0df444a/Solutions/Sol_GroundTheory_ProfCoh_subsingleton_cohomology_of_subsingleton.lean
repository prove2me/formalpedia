-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:07:54.868204+00:00
-- url     : https://prove2.me/submissions/1fdbb1fb-7b13-4530-a3ac-c6a0921ccac6

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_nsmul_cohomology_eq_zero

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
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A]
    [Subsingleton A] (n : ℕ) : Subsingleton (cohomology A n) := by
  refine ⟨fun x y => ?_⟩
  have h := nsmul_cohomology_eq_zero A (m := 1) (fun a => Subsingleton.elim _ _) n
  rw [← one_nsmul x, ← one_nsmul y, h, h]
end GroundTheory.ProfCoh
