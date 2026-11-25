-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_rtransL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:32.934025+00:00
-- url     : https://prove2.me/submissions/c7d99c3c-3979-48fb-90ae-8a793259b064

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
theorem _root_.solution [μ.IsMulRightInvariant] (ℓ : Module.Dual ℂ V) (g : G) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (rtransL g f) = contragredient ρ g (coeffL μ hρ ℓ f) := by
  refine Subtype.ext (LinearMap.ext fun v => ?_)
  rw [coeffL_apply, contragredient_apply_apply, coeffL_apply,
    heckeAct_apply_act μ f.2 (hρ v) g⁻¹]
  congr 2
  funext x
  simp
end GroundTheory.Automorphic.Whittaker
