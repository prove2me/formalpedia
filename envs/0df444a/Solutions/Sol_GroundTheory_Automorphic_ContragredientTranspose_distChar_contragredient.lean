-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.distChar_contragredient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:16.617325+00:00
-- url     : https://prove2.me/submissions/d07d679d-70d6-4ea6-b205-dc0e7358faa7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_distChar_eq_trace
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_heckeAct_contragredient_apply
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
import Theorems.Thm_GroundTheory_Automorphic_exists_forall_mul_left_mul_right
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
open GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MeasureTheory Module Whittaker
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution [μ.IsInvInvariant] (hρ : IsAdmissible ρ)
    (f : locallyConstantCompactSupport G ℂ ℂ) :
    distChar μ (contragredient ρ) (isAdmissible_contragredient hρ) f =
      distChar μ ρ hρ (compHomeoL (Homeomorph.inv G) f) := by
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left_mul_right f.2
  have hKl : ∀ k ∈ (K : Subgroup G), ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x :=
    fun k hk x => by simpa using hK k hk x 1 (one_mem _)
  have hKl' : ∀ k ∈ (K : Subgroup G), ∀ x,
      ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) (k * x) =
        ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) : G → ℂ) x := by
    intro k hk x
    have := hK 1 (one_mem _) x⁻¹ k⁻¹ (inv_mem hk)
    simpa [mul_inv_rev] using this
  rw [distChar_eq_trace μ (isAdmissible_contragredient hρ) f hKc K.isOpen hKl,
    distChar_eq_trace μ hρ _ hKc K.isOpen hKl']
  have := hρ.2 K hKc K.isOpen
  have := (isAdmissible_contragredient hρ).2 K hKc K.isOpen
  set e := fixedContragredientEquiv hρ.1 hKc K.isOpen
  refine (LinearMap.trace_conj' (R := ℂ) (M := fixedVectors (contragredient ρ) K)
    (N := Module.Dual ℂ (fixedVectors ρ K)) _ e).symm.trans ?_
  rw [← LinearMap.trace_transpose' (R := ℂ) (M := fixedVectors ρ K)]
  congr 1
  refine LinearMap.ext fun l => LinearMap.ext fun v => ?_
  have hw : heckeAct μ ρ ((compHomeoL (Homeomorph.inv G) f : locallyConstantCompactSupport G ℂ ℂ) :
      G → ℂ) (v : V) ∈ fixedVectors ρ K :=
    range_heckeLin_le μ hρ.1 _ hKl' (LinearMap.mem_range_self _ (v : V))
  have key := congrArg (fun L : Module.Dual ℂ (fixedVectors ρ K) => L ⟨_, hw⟩) (e.apply_symm_apply l)
  rw [LinearEquiv.conj_apply_apply]
  change ((heckeAct μ (contragredient ρ) (f : G → ℂ)
    ((e.symm l : fixedVectors (contragredient ρ) K) : smoothVectors (Representation.dual ρ)) :
      smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) (v : V) = l ⟨_, hw⟩
  rw [heckeAct_contragredient_apply μ hρ.1]
  exact key
end GroundTheory.Automorphic.ContragredientTranspose
