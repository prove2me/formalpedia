-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_central_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:45.900662+00:00
-- url     : https://prove2.me/submissions/d694e48f-49ae-459f-a93a-a795ce17a01f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Theorems.Thm_GroundTheory_Automorphic_algebraMap_intertwiningMap_bijective_of_isSmooth

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
open Polynomial Cardinal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) [ρ.IsIrreducible] {z : G}
    (hz : z ∈ Submonoid.center G) : ∃ c : ℂ, ∀ v : V, ρ z v = c • v := by
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth hρ).2
    (Representation.IntertwiningMap.centralMul ρ z hz)
  exact ⟨c, fun v => (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) hc).symm⟩
end GroundTheory.Automorphic
