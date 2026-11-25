-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:09:54.518571+00:00
-- url     : https://prove2.me/submissions/811ae137-a8a4-44ac-b1e2-6a7db7090d9e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character

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
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (hρ : IsAdmissible ρ) (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ ρ hρ f = finTrace (heckeLin μ hρ.1 f) := rfl
end GroundTheory.Automorphic.ContragredientTranspose
