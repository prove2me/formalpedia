-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rank_mul_rank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:45.570538+00:00
-- url     : https://prove2.me/submissions/07bc6a75-6d44-4aa8-bb19-56e8bda0cd1a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isIrreducible_contragredient
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_equivariantFunctionals_le_one
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isMulRightInvariant_of_isInvInvariant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ne_zero_doubleContragredient
import Theorems.Thm_GroundTheory_Automorphic_isAdmissible_contragredient


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
  [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace.SeparableSpace G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {σ : G ≃ₜ G} {H : Subgroup G} {χ : H → ℂ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσμ : μ.map σ = μ)
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals ρ χ) *
      Module.rank ℂ (equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹)) ≤ 1 := by
  have := isMulRightInvariant_of_isInvInvariant μ
  by_cases h₂ : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) = ⊥
  · rw [h₂, rank_bot, mul_zero]
    exact zero_le_one
  by_cases h₁ : equivariantFunctionals ρ χ = ⊥
  · rw [h₁, rank_bot, zero_mul]
    exact zero_le_one
  have := isIrreducible_contragredient h
  have r₁ := rank_equivariantFunctionals_le_one μ hσ hσμ hGK h h₂
  have r₂ := rank_equivariantFunctionals_le_one μ hσ hσμ (hGK.inv hσ)
    (isAdmissible_contragredient h) (exists_ne_zero_doubleContragredient h h₁)
  calc Module.rank ℂ (equivariantFunctionals ρ χ) *
        Module.rank ℂ (equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹))
      ≤ 1 * 1 := mul_le_mul' r₁ r₂
    _ = 1 := one_mul 1
end GroundTheory.Automorphic.Whittaker
