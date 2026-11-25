-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.ker_coeffL_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:01:25.02654+00:00
-- url     : https://prove2.me/submissions/ef7c9fa9-b7c5-425d-bb3c-3965ffa92073

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_compHomeoL_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_convS
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_compHomeoL_convS
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_zero_left
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffDist_biTranslL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_surjective
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_apply_heckeAct_normInd
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_ltransL_mem_coeffKer
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_ker_coeffL_eq
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
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible]
    {ℓ : Module.Dual ℂ V} (hℓ : ℓ ∈ equivariantFunctionals ρ χ) (hℓ0 : ℓ ≠ 0)
    {ℓt : Module.Dual ℂ (smoothVectors (Representation.dual ρ))}
    (hℓt : ℓt ∈ equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) (hℓt0 : ℓt ≠ 0) :
    LinearMap.ker (coeffL μ h.1 ℓ) = (coeffKer μ h.1 ℓt).comap (compHomeoL σ) := by
  have hB := hGK (coeffDist μ h.1 ℓ ℓt) (coeffDist_biTranslL μ h.1 hℓ hℓt)
  refine ker_coeffL_eq μ h ?_ ?_ ?_
  ·
    intro f₁ hf₁
    rw [LinearMap.mem_ker] at hf₁
    show compHomeoL σ f₁ ∈ coeffKer μ h.1 ℓt
    intro ξ
    obtain ⟨k, rfl⟩ := coeffL_surjective μ h hℓ0 ξ
    set f₂ := compHomeoL σ.symm k
    have hk : k = compHomeoL σ f₂ := (compHomeoL_symm_apply σ k).symm
    rw [← coeffL_convS, hk, ← compHomeoL_convS μ σ hσ hσμ]
    have := hB (convS μ f₁ f₂)
    simp only [coeffDist, LinearMap.comp_apply] at this
    rw [this, coeffL_convS, hf₁]
    simp [coeffL_zero_left]
  ·
    intro g f hf
    show compHomeoL σ (rtransL g f) ∈ coeffKer μ h.1 ℓt
    have e : compHomeoL σ (rtransL g f) = ltransL (σ.symm g)⁻¹ (compHomeoL σ f) :=
      Subtype.ext (funext fun x => by
        simp only [coe_compHomeoL, coe_rtransL, coe_ltransL, Function.comp_apply, inv_inv, hσ,
          Homeomorph.apply_symm_apply])
    rw [e]
    exact ltransL_mem_coeffKer μ h.1 _ hf
  ·
    intro htop
    obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ, ℓt ξ ≠ 0 := not_forall.1 fun e => hℓt0 (LinearMap.ext e)
    obtain ⟨K, hKc, hKo, hξK⟩ := (isSmooth_iff_forall_exists _).1 (isSmooth_contragredient ρ) ξ₀
    let k₀ : locallyConstantCompactSupport G ℂ ℂ := ⟨normInd μ K, normInd_mem μ hKc hKo⟩
    have hmem : compHomeoL σ.symm k₀ ∈ (coeffKer μ h.1 ℓt).comap (compHomeoL σ) := by
      rw [htop]
      exact Submodule.mem_top
    have h0 := (Submodule.mem_comap.1 hmem) ξ₀
    rw [compHomeoL_symm_apply] at h0
    have e : coeffL μ h.1 (ξ₀ : Module.Dual ℂ V) k₀ = ξ₀ :=
      Subtype.ext (LinearMap.ext fun v => apply_heckeAct_normInd μ h.1 hKc hKo hξK v)
    rw [e] at h0
    exact hξ₀ h0
end GroundTheory.Automorphic.Whittaker
