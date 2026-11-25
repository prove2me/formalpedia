-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.ker_coeffL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:38:12.277835+00:00
-- url     : https://prove2.me/submissions/f12980db-46c2-44a6-b75f-028690ee9a83

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_coeffL_rtransL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isIrreducible_contragredient

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
    {L : Submodule ℂ (locallyConstantCompactSupport G ℂ ℂ)}
    (hker : LinearMap.ker (coeffL μ h.1 ℓ) ≤ L) (hL : ∀ g, ∀ f ∈ L, rtransL g f ∈ L)
    (hLtop : L ≠ ⊤) : LinearMap.ker (coeffL μ h.1 ℓ) = L := by
  have := isIrreducible_contragredient h
  let M : Subrepresentation (contragredient ρ) :=
    ⟨L.map (coeffL μ h.1 ℓ), fun g ξ hξ => by
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hξ
      rw [← coeffL_rtransL]
      exact Submodule.mem_map_of_mem (hL g f hf)⟩
  refine le_antisymm hker ?_
  rcases eq_bot_or_eq_top M with hM | hM
  · intro f hf
    have : coeffL μ h.1 ℓ f ∈ M := Submodule.mem_map_of_mem hf
    rw [hM] at this
    exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 this)
  · exfalso
    apply hLtop
    refine eq_top_iff.2 fun f _ => ?_
    have : coeffL μ h.1 ℓ f ∈ M := by
      rw [hM]
      exact Submodule.mem_top
    obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 this
    have hd : f - f' ∈ L := hker (LinearMap.mem_ker.2 (by rw [map_sub, e, sub_self]))
    have := L.add_mem hd hf'
    rwa [sub_add_cancel] at this
end GroundTheory.Automorphic.Whittaker
