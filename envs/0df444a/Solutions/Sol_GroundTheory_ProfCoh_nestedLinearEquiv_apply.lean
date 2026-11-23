-- Prove2me | solution 1 for GroundTheory.ProfCoh.nestedLinearEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:27.4077+00:00
-- url     : https://prove2.me/submissions/38534cf2-dc2f-4940-ad21-59883af74925

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested

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
open CategoryTheory TopRep ContRepresentation
universe u v w
variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
variable (X : TopRep.{u} k G)
namespace GroundTheory.ProfCoh
theorem _root_.solution (m : ℕ) (a : resolutionX X m) :
    nestedLinearEquiv X m a = nestedHomeomorph X m a :=
  rfl
end GroundTheory.ProfCoh
