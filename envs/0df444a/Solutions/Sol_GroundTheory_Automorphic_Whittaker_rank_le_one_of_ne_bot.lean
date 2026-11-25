-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.rank_le_one_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:00:41.688572+00:00
-- url     : https://prove2.me/submissions/78d3a814-2b86-4ad8-b9f1-892dc71c1963

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_rank_equivariantFunctionals_le_one
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isMulRightInvariant_of_isInvInvariant

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
    (hGK : BiEquivariantSigmaInvariant H χ σ) (h : IsAdmissible ρ) [ρ.IsIrreducible]
    (hne : equivariantFunctionals (contragredient ρ) (fun g => (χ g)⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals ρ χ) ≤ 1 := by
  have := isMulRightInvariant_of_isInvInvariant μ
  exact rank_equivariantFunctionals_le_one μ hσ hσμ hGK h hne
end GroundTheory.Automorphic.Whittaker
