-- Prove2me | solution 1 for GroundTheory.ProfCoh.inflation_comp_cohomologyToGroupCohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:48:51.433307+00:00
-- url     : https://prove2.me/submissions/bbe4e994-c84f-4e26-9cb1-25d82991279f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs
import Theorems.Thm_P2M_GroundTheory_ProfCoh_inflationCochains_comp_cochainsComplex__38875cb65454

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
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : Rep.{u} k G)
variable [IsTopologicalGroup G] [IsDiscreteRep A]
namespace GroundTheory.ProfCoh
theorem _root_.solution (U : OpenNormalSubgroup G) (n : ℕ) :
    inflation A U n ≫ cohomologyToGroupCohomology A n =
      (groupCohomology.infNatTrans k (U : Subgroup G) n).app A := by
  unfold inflation cohomologyToGroupCohomology
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  rw [inflationCochains_comp_cochainsComplexι]
  rfl
end GroundTheory.ProfCoh
