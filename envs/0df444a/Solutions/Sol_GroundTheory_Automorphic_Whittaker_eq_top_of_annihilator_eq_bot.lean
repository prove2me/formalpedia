-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.eq_top_of_annihilator_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:22.265844+00:00
-- url     : https://prove2.me/submissions/ab173722-8cef-4897-bfb1-4e5bb8718e42

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_forall_mem_apply_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_isSmooth_contragredient
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
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : IsAdmissible ρ) {W : Subrepresentation (contragredient ρ)}
    (hA : annihilatorSubrep W = ⊥) : W = ⊤ := by
  have hsm := isSmooth_contragredient ρ
  refine Subrepresentation.ext (eq_top_iff.2 fun ξ _ => ?_)
  obtain ⟨K, hKc, hKo, hξK⟩ := (isSmooth_iff_forall_exists _).1 hsm ξ
  have hfin : FiniteDimensional ℂ (fixedVectors ρ K) := h.2 K hKc hKo
  have hfinD : FiniteDimensional ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
    (Module.finite_dual_iff ℂ).2 hfin
  let S : Submodule ℂ (Module.Dual ℂ (fixedVectors ρ K)) :=
    (W.toSubmodule.comap (fixedVectors (contragredient ρ) K).subtype).map (restrictFixed ρ K)
  have hSfin : FiniteDimensional ℂ S := FiniteDimensional.finiteDimensional_submodule S
  have hS : S = ⊤ := by
    by_contra hS
    have hco : S.dualCoannihilator ≠ ⊥ := by
      intro e
      apply hS
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S), e,
        Submodule.dualAnnihilator_bot]
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hco
    have hann : (u : V) ∈ annihilatorSubrep W := by
      refine forall_mem_apply_eq_zero hKc hKo u.2 fun η hη hηK => ?_
      have hmem : restrictFixed ρ K ⟨η, hηK⟩ ∈ S := Submodule.mem_map_of_mem hη
      exact (Submodule.mem_dualCoannihilator _).1 hu _ hmem
    rw [hA] at hann
    exact hu0 (Subtype.ext ((Submodule.mem_bot ℂ).1 hann))
  have hmem : restrictFixed ρ K ⟨ξ, hξK⟩ ∈ S := by
    rw [hS]
    exact Submodule.mem_top
  obtain ⟨η, hη, hηξ⟩ := Submodule.mem_map.1 hmem
  have e := (restrictFixed_bijective h.1 hKc hKo).1 hηξ
  have : (η : smoothVectors (Representation.dual ρ)) = ξ := congrArg Subtype.val e
  rw [← this]
  exact hη
end GroundTheory.Automorphic.Whittaker
