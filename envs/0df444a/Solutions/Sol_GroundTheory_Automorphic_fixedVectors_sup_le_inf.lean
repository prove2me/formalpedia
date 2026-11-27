-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedVectors_sup_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:52.715431+00:00
-- url     : https://prove2.me/submissions/a9cb76b8-cf6d-4d9a-a09c-079f01fdf416

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_fixedVectors_antitone

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
theorem _root_.solution (K L : Subgroup G) :
    fixedVectors ρ K ⊔ fixedVectors ρ L ≤ fixedVectors ρ (K ⊓ L) :=
  sup_le (fixedVectors_antitone ρ inf_le_left) (fixedVectors_antitone ρ inf_le_right)
end GroundTheory.Automorphic
