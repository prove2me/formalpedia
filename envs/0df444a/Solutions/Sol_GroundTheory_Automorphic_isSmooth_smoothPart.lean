-- Prove2me | solution 1 for GroundTheory.Automorphic.isSmooth_smoothPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:42.455027+00:00
-- url     : https://prove2.me/submissions/354a309b-ec4a-49ea-8d97-6a10a9498203

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
theorem _root_.solution : IsSmooth (smoothPart ρ) := by
  intro v
  have : (stabilizerOf (smoothPart ρ) v : Set G) = stabilizerOf ρ (v : V) := by
    ext g
    simp [mem_stabilizerOf, Subtype.ext_iff]
  rw [this]
  exact v.2
end GroundTheory.Automorphic
