-- Prove2me | solution 1 for GroundTheory.ProfCoh.isOpen_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:36.81381+00:00
-- url     : https://prove2.me/submissions/19064e77-2c4d-47f4-9ac4-bc43ae497f3d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a
end GroundTheory.ProfCoh
