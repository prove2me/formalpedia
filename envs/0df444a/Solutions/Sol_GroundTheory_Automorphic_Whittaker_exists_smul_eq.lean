-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:06:51.652719+00:00
-- url     : https://prove2.me/submissions/f09fa5ca-40de-4eaa-87e2-272c13dbe6ca

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_rtransL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_normInd_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isIrreducible_contragredient
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_surjective
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_ker_coeffL_eq_comap
import Theorems.Thm_GroundTheory_Automorphic_algebraMap_intertwiningMap_bijective_of_isSmooth
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists


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
variable [μ.IsInvInvariant] {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) [TopologicalSpace.SeparableSpace G]
    (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0)
    {ℓ₁ ℓ₂ : Module.Dual ℂ V} (h₁ : ℓ₁ ∈ equivariantFunctionals ρ χ) (h₁0 : ℓ₁ ≠ 0)
    (h₂ : ℓ₂ ∈ equivariantFunctionals ρ χ) : ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  by_cases h₂0 : ℓ₂ = 0
  · exact ⟨0, by rw [h₂0, zero_smul]⟩
  have := isIrreducible_contragredient h
  set A₁ := coeffL μ h.1 ℓ₁
  set A₂ := coeffL μ h.1 ℓ₂
  have hs₁ : Function.Surjective A₁ := coeffL_surjective μ h h₁0
  have hker : LinearMap.ker A₁ ≤ LinearMap.ker A₂ := by
    rw [ker_coeffL_eq_comap μ hσ hσμ hGK h h₁ h₁0 hℓt hℓt0,
      ker_coeffL_eq_comap μ hσ hσμ hGK h h₂ h₂0 hℓt hℓt0]
  let e := A₁.quotKerEquivOfSurjective hs₁
  let T : smoothVectors (Representation.dual ρ) →ₗ[ℂ] smoothVectors (Representation.dual ρ) :=
    (LinearMap.ker A₁).liftQ A₂ hker ∘ₗ e.symm.toLinearMap
  have hT : ∀ f, T (A₁ f) = A₂ f := fun f => by
    have : e.symm (A₁ f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hTi : ∀ (g : G) (ξ : smoothVectors (Representation.dual ρ)),
      T (contragredient ρ g ξ) = contragredient ρ g (T ξ) := fun g ξ => by
    obtain ⟨f, rfl⟩ := hs₁ ξ
    rw [← coeffL_rtransL, hT, hT, coeffL_rtransL]
  obtain ⟨c, hc⟩ := (algebraMap_intertwiningMap_bijective_of_isSmooth
    (isSmooth_contragredient ρ)).2 (LinearMap.intertwiningMap_of_isIntertwiningMap _ _ T hTi)
  have hTc : ∀ ξ, T ξ = c • ξ := fun ξ =>
    (congrArg (fun F : Representation.IntertwiningMap (contragredient ρ) (contragredient ρ) =>
      F ξ) hc).symm
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
  let k : locallyConstantCompactSupport G ℂ ℂ := ⟨normInd μ K, normInd_mem μ hKc hKo⟩
  have e₂ := coeffL_normInd_apply μ h.1 ℓ₂ hKc hKo hvK
  have e₁ := coeffL_normInd_apply μ h.1 ℓ₁ hKc hKo hvK
  rw [LinearMap.smul_apply, ← e₁, ← e₂]
  change ((A₂ k : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v =
    c • ((A₁ k : smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v
  rw [← hT, hTc]
  rfl
end GroundTheory.Automorphic.Whittaker
