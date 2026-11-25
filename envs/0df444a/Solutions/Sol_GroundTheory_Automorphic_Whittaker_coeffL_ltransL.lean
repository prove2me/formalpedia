-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_ltransL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:51.897944+00:00
-- url     : https://prove2.me/submissions/812b335b-f43a-4b78-aa52-f12a5bf225b0

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
theorem _root_.solution [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (a : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (ltransL a f) = coeffL μ hρ (ℓ ∘ₗ ρ a) f := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, coeffL_apply, LinearMap.comp_apply, heckeAct_ltrans a f.2 (hρ v)]
  rfl
end GroundTheory.Automorphic.Whittaker
