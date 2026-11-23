-- Prove2me | solution 1 for GroundTheory.ProfCoh.isDiscreteRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:46.45402+00:00
-- url     : https://prove2.me/submissions/a6f7beb1-7d86-4e0c-8513-6321b3ea139e

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
theorem _root_.solution (A : Rep.{w} k G) : isDiscreteRep k G A ↔ IsDiscreteRep A :=
  Iff.rfl
end GroundTheory.ProfCoh
