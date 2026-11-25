-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.coeffL_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:14:33.437437+00:00
-- url     : https://prove2.me/submissions/7ddcb6c3-3ab5-427b-a821-98c0e7de9526

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_rtransL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_normInd_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isIrreducible_contragredient
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
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : IsAdmissible ρ) [ρ.IsIrreducible] {ℓ : Module.Dual ℂ V}
    (hℓ : ℓ ≠ 0) : Function.Surjective (coeffL μ h.1 ℓ) := by
  have := isIrreducible_contragredient h
  let R : Subrepresentation (contragredient ρ) :=
    ⟨LinearMap.range (coeffL μ h.1 ℓ), fun g ξ hξ => by
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.1 hξ
      rw [← coeffL_rtransL]
      exact LinearMap.mem_range_self _ _⟩
  rcases eq_bot_or_eq_top R with hR | hR
  · exfalso
    obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := not_forall.1 fun e => hℓ (LinearMap.ext e)
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    have hmem : coeffL μ h.1 ℓ ⟨normInd μ K, normInd_mem μ hKc hKo⟩ ∈ R :=
      LinearMap.mem_range_self _ _
    rw [hR] at hmem
    have h0 := (Submodule.mem_bot ℂ).1 hmem
    apply hv
    rw [← coeffL_normInd_apply μ h.1 ℓ hKc hKo hvK, h0]
    rfl
  · intro ξ
    have : ξ ∈ R := by
      rw [hR]
      exact Submodule.mem_top
    exact LinearMap.mem_range.1 this
end GroundTheory.Automorphic.Whittaker
