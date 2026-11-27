-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_coe_invariantsToQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:49:30.040177+00:00
-- url     : https://prove2.me/submissions/090979d3-5b83-4a83-97e1-03e6950bcf19

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation

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
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] {A : Rep ℤ G} (S : Subgroup G) [S.Normal]
namespace GroundTheory.ProfCoh
theorem _root_.solution (a : A.ρ.invariants) :
    (invariantsToQuotient S a).1.1 = (a : A) :=
  rfl
end GroundTheory.ProfCoh
