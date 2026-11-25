-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.forall_mem_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:53.010432+00:00
-- url     : https://prove2.me/submissions/41057253-2197-42fd-8803-f0b951e47947

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_fixedProj_mem_subrep
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsKer_le_ker_of_invariant
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors
import Theorems.Thm_GroundTheory_Automorphic_sub_fixedProj_mem


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
theorem _root_.solution {W : Subrepresentation (contragredient ρ)} {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {u : V} (hu : u ∈ fixedVectors ρ K)
    (hW : ∀ η ∈ W, η ∈ fixedVectors (contragredient ρ) K → (η : Module.Dual ℂ V) u = 0) :
    ∀ ζ ∈ W, (ζ : Module.Dual ℂ V) u = 0 := by
  intro ζ hζ
  have hsm := isSmooth_contragredient ρ
  let E : smoothVectors (Representation.dual ρ) →ₗ[ℂ] ℂ :=
    LinearMap.applyₗ (R := ℂ) u ∘ₗ (smoothVectors (Representation.dual ρ)).subtype
  have hE : ∀ k ∈ K, ∀ η, E (contragredient ρ k η) = E η := fun k hk η => by
    change ((contragredient ρ k η : smoothVectors (Representation.dual ρ)) :
      Module.Dual ℂ V) u = (η : Module.Dual ℂ V) u
    rw [contragredient_apply_apply, mem_fixedVectors.1 hu k⁻¹ (inv_mem hk)]
  have e1 : (ζ : Module.Dual ℂ V) u =
      (((fixedProj (contragredient ρ) hsm hKc hKo ζ : fixedVectors _ K) :
        smoothVectors (Representation.dual ρ)) : Module.Dual ℂ V) u := by
    have := coinvariantsKer_le_ker_of_invariant hE (sub_fixedProj_mem hsm hKc hKo ζ)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this
  rw [e1]
  exact hW _ (fixedProj_mem_subrep hsm W hKc hKo hζ) (fixedProj (contragredient ρ) hsm hKc hKo ζ).2
end GroundTheory.Automorphic.Whittaker
