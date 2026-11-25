-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isSmooth_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:20:54.595678+00:00
-- url     : https://prove2.me/submissions/850105a1-58f0-44be-9517-8729d79bc9b8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion

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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hρ : IsSmooth ρ) (W : Subrepresentation ρ) :
    IsSmooth (V := W.toSubmodule) W.toRepresentation := fun w => by
  have : (stabilizerOf (V := W.toSubmodule) W.toRepresentation w : Set G) =
      stabilizerOf ρ (w : V) := by
    ext g
    simp only [SetLike.mem_coe, mem_stabilizerOf, Subtype.ext_iff]
    rfl
  rw [this]
  exact hρ _
end GroundTheory.Automorphic.Whittaker
