-- Prove2me | solution 1 for GroundTheory.ProfCoh.levelFunctor_obj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:49:17.734706+00:00
-- url     : https://prove2.me/submissions/08866baa-d968-4386-97eb-1a6d1155fc23

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs

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
namespace GroundTheory.ProfCoh
theorem _root_.solution (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (levelFunctor A n).obj U = groupCohomology (A.quotientToInvariants (U.unop : Subgroup G)) n :=
  rfl
end GroundTheory.ProfCoh
