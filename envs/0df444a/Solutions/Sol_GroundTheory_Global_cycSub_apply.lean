-- Prove2me | solution 1 for GroundTheory.Global.cycSub_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:13:50.451686+00:00
-- url     : https://prove2.me/submissions/2265ea51-3ce4-48de-b7b5-50bb5324633e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G M : Type*} [Group G] [AddCommGroup M]
namespace GroundTheory.Global
theorem _root_.solution (ρ : Representation ℤ G M) (σ : G) (x : M) :
    cycSub ρ σ x = ρ σ x - x :=
  rfl
end GroundTheory.Global
