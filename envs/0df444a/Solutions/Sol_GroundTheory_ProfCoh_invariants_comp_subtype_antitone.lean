-- Prove2me | solution 1 for GroundTheory.ProfCoh.invariants_comp_subtype_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:42:18.824513+00:00
-- url     : https://prove2.me/submissions/2787a946-c7b8-411c-a3a5-a86049d24af5

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
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{w} k G) {U V : Subgroup G} (h : U ≤ V) :
    Representation.invariants (A.ρ.comp V.subtype) ≤ Representation.invariants (A.ρ.comp U.subtype) := by
  intro a ha
  rw [mem_invariants_comp_subtype_iff] at *
  exact h.trans ha
end GroundTheory.ProfCoh
