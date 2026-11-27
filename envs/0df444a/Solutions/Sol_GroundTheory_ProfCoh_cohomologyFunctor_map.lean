-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyFunctor_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:42.420693+00:00
-- url     : https://prove2.me/submissions/b6f36a53-0c2b-4c6e-bdef-7b933e1f7cfb

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
variable (k G)
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) {A B : DiscreteRep.{u} k G} (f : A ⟶ B) :
    (cohomologyFunctor k G n).map f = cohomologyMap f.hom n :=
  rfl
end GroundTheory.ProfCoh
