-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_of_sub_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:22.863056+00:00
-- url     : https://prove2.me/submissions/335c36fb-0b63-4b9f-bb02-6bf7ab88ce8b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_P2M_GroundTheory_ProfCoh_subsingleton_cohomology_X__77ff456b320e
import Theorems.Thm_GroundTheory_ProfCoh_subQuotShortComplex_shortExact

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
theorem _root_.solution (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) (n : ℕ)
    (h₁ : Subsingleton (cohomology (A.subrepresentation W h) n))
    (h₃ : Subsingleton (cohomology (A.quotient W h) n)) : Subsingleton (cohomology A n) :=
  subsingleton_cohomology_X₂ (subQuotShortComplex_shortExact A W h) n h₁ h₃
end GroundTheory.ProfCoh
