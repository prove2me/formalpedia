-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rank_equivariantFunctionals_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:36:55.485797+00:00
-- url     : https://prove2.me/submissions/66e8b038-fa83-488c-876b-c26fe7b889bc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_smul_eq

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
theorem _root_.solution (hσ : ∀ x y, σ (x * y) = σ y * σ x)
    (hσμ : μ.map σ = μ) (hGK : BiEquivariantSigmaInvariant H χ σ)
    [TopologicalSpace.SeparableSpace G] (h : IsAdmissible ρ) [ρ.IsIrreducible]
    (hne : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals ρ χ) ≤ 1 := by
  obtain ⟨ℓt, hℓt, hℓt0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [rank_le_one_iff]
  by_cases hz : ∀ ℓ ∈ equivariantFunctionals ρ χ, ℓ = 0
  · refine ⟨0, fun ℓ => ⟨0, ?_⟩⟩
    rw [zero_smul]
    exact Subtype.ext (hz ℓ ℓ.2).symm
  · push Not at hz
    obtain ⟨ℓ₁, h₁, h₁0⟩ := hz
    refine ⟨⟨ℓ₁, h₁⟩, fun ℓ => ?_⟩
    obtain ⟨c, hc⟩ := exists_smul_eq μ hσ hσμ hGK h hℓt hℓt0 h₁ h₁0 ℓ.2
    exact ⟨c, Subtype.ext hc.symm⟩
end GroundTheory.Automorphic.Whittaker
