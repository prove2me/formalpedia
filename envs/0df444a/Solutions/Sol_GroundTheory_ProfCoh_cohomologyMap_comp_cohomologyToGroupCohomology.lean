-- Prove2me | solution 1 for GroundTheory.ProfCoh.cohomologyMap_comp_cohomologyToGroupCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:52.715291+00:00
-- url     : https://prove2.me/submissions/66a1671f-f324-4486-8aa0-edb728723823

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Theorems.Thm_P2M_GroundTheory_ProfCoh_cochainsMap_comp_cochainsComplex__9cf709e5bb52

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
theorem _root_.solution {B : Rep.{u} k G} [IsDiscreteRep B]
    (f : A ⟶ B) (n : ℕ) :
    cohomologyMap f n ≫ cohomologyToGroupCohomology B n =
      cohomologyToGroupCohomology A n ≫ groupCohomology.map (MonoidHom.id G) f n := by
  change HomologicalComplex.homologyMap (cochainsMap f) n ≫
      HomologicalComplex.homologyMap (cochainsComplexι B) n =
    HomologicalComplex.homologyMap (cochainsComplexι A) n ≫
      HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) f) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_cochainsComplexι]
end GroundTheory.ProfCoh
