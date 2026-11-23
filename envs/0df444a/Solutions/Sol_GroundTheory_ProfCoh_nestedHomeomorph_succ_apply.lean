-- Prove2me | solution 1 for GroundTheory.ProfCoh.nestedHomeomorph_succ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:24.709434+00:00
-- url     : https://prove2.me/submissions/eb2c87e9-e0a2-4e6e-a2f0-465726597303

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
theorem _root_.solution (m : ℕ) (f : resolutionX X (m + 1))
    (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) f x =
      nestedHomeomorph X m ((f : C(G, resolutionX X m)) (x 0)) (Fin.tail x) :=
  rfl
end GroundTheory.ProfCoh
