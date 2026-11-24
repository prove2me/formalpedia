-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:59:15.51499+00:00
-- url     : https://prove2.me/submissions/8f0a3377-03c0-47f7-adb8-9531fa4088d9

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
variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
namespace GroundTheory.ProfCoh
theorem _root_.solution (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    cohomologyMap (f ≫ g) n = cohomologyMap f n ≫ cohomologyMap g n := by
  rw [cohomologyMap, cochainsMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ _
end GroundTheory.ProfCoh
