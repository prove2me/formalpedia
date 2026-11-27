-- Prove2me | solution 1 for GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_cdp_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:50:54.844121+00:00
-- url     : https://prove2.me/submissions/eb886af4-4c3a-49ad-a74c-5eea6b04158c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Theorems.Thm_GroundTheory_ProfCoh_cdp_le_iff

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
universe u
variable (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {p G}
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) {q : ℕ} (hq : cdp p G < q) :
    AddCommGroup.primaryComponent (cohomology A q) p = ⊥ :=
  cdp_le_iff.1 le_rfl A hA q hq
end GroundTheory.ProfCoh
