-- Prove2me | solution 1 for GroundTheory.ProfCoh.isDiscreteRep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:17:00.82026+00:00
-- url     : https://prove2.me/submissions/8303f7aa-ebd3-4108-ab28-2806205557db

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer

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
theorem _root_.solution (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩
end GroundTheory.ProfCoh
