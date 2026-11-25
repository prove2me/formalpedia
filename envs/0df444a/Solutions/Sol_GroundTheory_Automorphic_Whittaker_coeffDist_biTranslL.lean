-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffDist_biTranslL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:24:23.905857+00:00
-- url     : https://prove2.me/submissions/998c9a21-5505-4713-8c81-a167e04e336f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_biTranslL

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
    (hℓ : ℓ ∈ equivariantFunctionals ρ χ)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun h => (χ h)⁻¹))
    (f : locallyConstantCompactSupport G ℂ ℂ) (h₁ h₂ : H) :
    coeffDist μ hρ ℓ ℓt (biTranslL (h₁ : G) (h₂ : G) f) = χ h₁ * (χ h₂)⁻¹ * coeffDist μ hρ ℓ ℓt f := by
  simp only [coeffDist, LinearMap.comp_apply]
  rw [coeffL_biTranslL μ hρ hℓ, map_smul, hℓt h₂, smul_eq_mul, mul_assoc]
end GroundTheory.Automorphic.Whittaker
