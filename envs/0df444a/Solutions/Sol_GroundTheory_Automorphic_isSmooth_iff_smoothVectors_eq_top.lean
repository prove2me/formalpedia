-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_iff_smoothVectors_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:18.567795+00:00
-- url     : https://prove2.me/submissions/44517bd5-99a6-49dd-a750-4b8c76295a1e

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
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GroundTheory.Automorphic
theorem _root_.solution : IsSmooth ρ ↔ smoothVectors ρ = ⊤ := by
  rw [eq_top_iff]
  exact ⟨fun h v _ => h v, fun h v => h Submodule.mem_top⟩
end GroundTheory.Automorphic
