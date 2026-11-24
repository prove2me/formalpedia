-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedVectors_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:37.505493+00:00
-- url     : https://prove2.me/submissions/bebfc943-0e4f-4de1-b15a-7fdc1f96782d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep

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
theorem _root_.solution {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    fixedVectors ρ H₂ ≤ fixedVectors ρ H₁ :=
  fun _ hv g hg => hv g (h hg)
end GroundTheory.Automorphic
