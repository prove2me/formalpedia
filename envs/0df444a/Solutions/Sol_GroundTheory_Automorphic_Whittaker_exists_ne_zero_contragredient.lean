-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_ne_zero_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:23.453885+00:00
-- url     : https://prove2.me/submissions/6a0c5613-cc6f-43a9-b593-1c10cb5b18a9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists
import Theorems.Thm_GroundTheory_Automorphic_restrictFixed_apply


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
theorem _root_.solution (h : IsAdmissible ρ) {v : V} (hv : v ≠ 0) :
    ∃ ξ : smoothVectors (Representation.dual ρ), (ξ : Module.Dual ℂ V) v ≠ 0 := by
  obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
  have hv' : (⟨v, hvK⟩ : fixedVectors ρ K) ≠ 0 := fun e => hv (congrArg Subtype.val e)
  obtain ⟨φ, hφ⟩ := not_forall.1
    (mt (Module.forall_dual_apply_eq_zero_iff ℂ (⟨v, hvK⟩ : fixedVectors ρ K)).1 hv')
  obtain ⟨ξ, hξ⟩ := (restrictFixed_bijective h.1 hKc hKo).2 φ
  refine ⟨(ξ : smoothVectors (Representation.dual ρ)), fun e => hφ ?_⟩
  rw [← hξ, restrictFixed_apply]
  exact e
end GroundTheory.Automorphic.Whittaker
