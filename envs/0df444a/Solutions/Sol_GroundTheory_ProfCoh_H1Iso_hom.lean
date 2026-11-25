-- Prove2me | solution 1 for GroundTheory.ProfCoh.H1Iso_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:17.11749+00:00
-- url     : https://prove2.me/submissions/dfe1f3bf-2c47-4186-9e65-abdc895609bd

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic

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
open CategoryTheory Limits groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{u} k G) [IsDiscreteRep A] {σ : G}
variable [CompactSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (hσ : IsZHatGenerator σ) (hA : IsAddTorsion A) :
    (H1Iso A hσ hA).hom = H1Eval A σ :=
  rfl
end GroundTheory.ProfCoh
