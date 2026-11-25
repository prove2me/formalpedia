-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_biTranslL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:04.83973+00:00
-- url     : https://prove2.me/submissions/edbc541d-4e7e-4eae-b5bd-5aedb0127173

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_biTranslL_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_rtransL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_ltransL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_smul_left

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
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {H : Subgroup G} {χ : H → ℂ} {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ∈ equivariantFunctionals ρ χ) (h₁ h₂ : H) (f : locallyConstantCompactSupport G ℂ ℂ) :
    coeffL μ hρ ℓ (biTranslL (h₁ : G) (h₂ : G) f) =
      χ h₁ • contragredient ρ h₂ (coeffL μ hρ ℓ f) := by
  have e : ℓ ∘ₗ ρ h₁ = χ h₁ • ℓ := LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hℓ h₁ v
  rw [biTranslL_eq, coeffL_ltransL, e, coeffL_smul_left, coeffL_rtransL]
end GroundTheory.Automorphic.Whittaker
