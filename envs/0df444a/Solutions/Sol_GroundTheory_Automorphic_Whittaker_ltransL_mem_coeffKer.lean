-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.ltransL_mem_coeffKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:46:43.643436+00:00
-- url     : https://prove2.me/submissions/c8edeaab-73d2-479a-9620-d60fa668a19b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_ltransL

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
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hρ : IsSmooth ρ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))} (a : G)
    {k : locallyConstantCompactSupport G ℂ ℂ} (hk : k ∈ coeffKer μ hρ ℓt) :
    ltransL a k ∈ coeffKer μ hρ ℓt := by
  intro ξ
  rw [coeffL_ltransL]
  have e : (ξ : Module.Dual ℂ V) ∘ₗ ρ a =
      ((contragredient ρ a⁻¹ ξ : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) :=
    LinearMap.ext fun v => by rw [contragredient_apply_apply, inv_inv]; rfl
  rw [e]
  exact hk _
end GroundTheory.Automorphic.Whittaker
