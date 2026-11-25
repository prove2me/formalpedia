-- Prove2me | solution 1 for GroundTheory.Automorphic.toDoubleContragredient_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:24.130444+00:00
-- url     : https://prove2.me/submissions/9aa8f444-9145-4ae6-8488-97ca116f21e7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient
import Theorems.Thm_GroundTheory_Automorphic_restrictFixed_apply
import Theorems.Thm_GroundTheory_Automorphic_fixedContragredientEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_eq_of_invariant_of_eqOn
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_iff_forall_exists
import Theorems.Thm_GroundTheory_Automorphic_mem_smoothVectors_iff


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
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution (h : IsAdmissible ρ) :
    Function.Bijective (toDoubleContragredient h.1) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨K, hKc, hKo, hvK⟩ := (isSmooth_iff_forall_exists ρ).1 h.1 v
    set e := fixedContragredientEquiv h.1 hKc hKo
    have hzero : (⟨v, hvK⟩ : fixedVectors ρ K) = 0 := by
      refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun μ => ?_
      have h1 : (((e.symm μ : fixedVectors (contragredient ρ) K) :
          smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) v = 0 := by
        have := congrArg (fun Φ : smoothVectors (Representation.dual (contragredient ρ)) =>
          (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ)))
            (e.symm μ : fixedVectors (contragredient ρ) K)) hv
        exact this
      have h2 : e (e.symm μ) = μ := e.apply_symm_apply μ
      rw [← h2, fixedContragredientEquiv_apply, restrictFixed_apply]
      exact h1
    simpa using congrArg Subtype.val hzero
  · intro Φ
    obtain ⟨K, hKc, hKo, hΦK⟩ := (mem_smoothVectors_iff _).1 Φ.2
    set e := fixedContragredientEquiv h.1 hKc hKo
    have := h.2 K hKc hKo
    let ψ : Module.Dual ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
      (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) ∘ₗ
        (fixedVectors (contragredient ρ) K).subtype ∘ₗ e.symm.toLinearMap
    set w := (Module.evalEquiv ℂ (fixedVectors ρ K)).symm ψ
    have hw : ∀ μ : Module.Dual ℂ (fixedVectors ρ K), μ w = ψ μ := fun μ =>
      LinearMap.congr_fun ((Module.evalEquiv ℂ (fixedVectors ρ K)).apply_symm_apply ψ) μ
    refine ⟨(w : V), Subtype.ext ?_⟩
    refine eq_of_invariant_of_eqOn (isSmooth_contragredient ρ) hKc hKo (fun k hk x => ?_)
      (mem_fixedVectors_dual.1 hΦK) fun x hx => ?_
    · change (x : Module.Dual ℂ V) (ρ k⁻¹ w) = (x : Module.Dual ℂ V) w
      rw [w.2 _ (inv_mem hk)]
    · have h1 : (Φ : Module.Dual ℂ (smoothVectors (Representation.dual ρ))) x =
          ψ (e ⟨x, hx⟩) := by
        simp [ψ]
      rw [h1, ← hw]
      rfl
end GroundTheory.Automorphic
