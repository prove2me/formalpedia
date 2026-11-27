-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyIsoGroupCohomology_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:49.475821+00:00
-- url     : https://prove2.me/submissions/07477c1a-947b-4980-9a4e-805b9ab8572b

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality

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
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A : Rep.{u} k G) [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution [DiscreteTopology G] (n : ℕ) :
    (cohomologyIsoGroupCohomology A n).hom = cohomologyToGroupCohomology A n :=
  rfl
end GroundTheory.ProfCoh
