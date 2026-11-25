-- Prove2me | solution 1 for GroundTheory.ProfCoh.IsDiscreteRep.of_forall_exists_mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:22:55.734205+00:00
-- url     : https://prove2.me/submissions/ca253aac-3cc9-4c1f-a68d-9fcd6fffce09

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Theorems.Thm_GroundTheory_ProfCoh_mem_invariants_comp_subtype_iff

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
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
namespace IsDiscreteRep
theorem _root_.solution (A : Rep.{w} k G)
    (h : ∀ a : A, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ a ∈ Representation.invariants (A.ρ.comp U.subtype)) :
    IsDiscreteRep A :=
  ⟨fun a => by
    obtain ⟨U, hU, ha⟩ := h a
    exact Subgroup.isOpen_mono ((mem_invariants_comp_subtype_iff A U a).1 ha) hU⟩
end IsDiscreteRep
end GroundTheory.ProfCoh
