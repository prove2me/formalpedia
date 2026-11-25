-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.isIrreducible_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:06:35.842251+00:00
-- url     : https://prove2.me/submissions/2b418714-8425-4841-86ba-44f0ef1a9049

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_ne_zero_contragredient
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_top_of_annihilator_eq_bot
import Theorems.Thm_GroundTheory_Automorphic_exists_ne_zero_of_isIrreducible


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
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : IsAdmissible ρ) [ρ.IsIrreducible] :
    (contragredient ρ).IsIrreducible := by
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ : smoothVectors (Representation.dual ρ), ξ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := ρ)
    obtain ⟨ξ, hξ⟩ := exists_ne_zero_contragredient h hv
    exact ⟨ξ, fun e => hξ (by rw [e]; rfl)⟩
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => hξ₀ ?_⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have : ξ₀ ∈ (⊤ : Subrepresentation (contragredient ρ)) := Submodule.mem_top
    rw [← e] at this
    exact (Submodule.mem_bot ℂ).1 this
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  rcases eq_bot_or_eq_top (annihilatorSubrep W) with hA | hA
  · exact eq_top_of_annihilator_eq_bot h hA
  · exfalso
    apply hW
    refine Subrepresentation.ext (eq_bot_iff.2 fun ξ hξ => ?_)
    rw [Submodule.mem_bot]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : v ∈ annihilatorSubrep W := by
      rw [hA]
      exact Submodule.mem_top
    exact hv ξ hξ
end GroundTheory.Automorphic.Whittaker
