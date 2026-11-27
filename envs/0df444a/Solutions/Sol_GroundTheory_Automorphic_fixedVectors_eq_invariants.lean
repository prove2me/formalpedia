-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedVectors_eq_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:30.61489+00:00
-- url     : https://prove2.me/submissions/0db36d8d-9632-4617-9460-c5212b54a250

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V)
namespace GroundTheory.Automorphic
theorem _root_.solution (H : Subgroup G) :
    fixedVectors ρ H = Representation.invariants (ρ.comp H.subtype) := by
  ext v
  simp [mem_fixedVectors, Representation.mem_invariants]
end GroundTheory.Automorphic
