-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_convS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:14:03.858004+00:00
-- url     : https://prove2.me/submissions/655ddd89-3129-4d8e-96f3-7f8a88bb5c02

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_apply

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
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
variable (hρ : IsSmooth ρ)
include hρ
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (f₁ f₂ : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (convS μ f₁ f₂) =
      coeffL μ hρ ((coeffL μ hρ ℓ f₁ : smoothVectors (Representation.dual ρ)) :
        Module.Dual ℂ V) f₂ := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, coeffL_apply, coeffL_apply, convS, heckeAct_groupConv f₁.2 f₂.2 (hρ v)]
end GroundTheory.Automorphic.Whittaker
