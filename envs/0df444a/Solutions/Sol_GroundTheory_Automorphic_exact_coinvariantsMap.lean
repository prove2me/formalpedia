-- Prove2me | solution 1 for GroundTheory.Automorphic.exact_coinvariantsMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:24.85461+00:00
-- url     : https://prove2.me/submissions/43fc2228-0359-4db7-a5a9-e73c548c9764

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsKer_le_ker
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_coinvariantsKer
import Theorems.Thm_GroundTheory_Automorphic_coe_fixedMap_apply
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem_coinvariantsKer
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_map
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
open Set Filter Topology
variable {N : Type*} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
  [LocallyCompactSpace N] [T2Space N] [TotallyDisconnectedSpace N]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ N V)
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ N W} {τ : Representation ℂ N X}
namespace GroundTheory.Automorphic
theorem _root_.solution
    (hN : ∀ s : Finset N, ∃ K : Subgroup N, IsCompact (K : Set N) ∧ IsOpen (K : Set N) ∧
      ∀ x ∈ s, x ∈ K)
    (hσ : IsSmooth σ) (hτ : IsSmooth τ)
    (f : Representation.IntertwiningMap ρ σ) (g : Representation.IntertwiningMap σ τ)
    (hfg : Function.Exact f g) :
    Function.Exact (Representation.Coinvariants.map ρ σ f)
      (Representation.Coinvariants.map σ τ g) := by
  intro y
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  rw [Representation.Coinvariants.map_mk]
  constructor
  · intro h0
    rw [Representation.Coinvariants.mk_eq_zero] at h0
    obtain ⟨K, hKc, hKo, hK⟩ := exists_mem_coinvariantsKer τ hN h0
    have h1 : g (fixedProj σ hσ hKc hKo w : W) = 0 := by
      have := congrArg Subtype.val (fixedProj_map hKc hKo hσ hτ g w)
      rw [fixedProj_apply_of_mem_coinvariantsKer hτ hKc hKo hK, coe_fixedMap_apply] at this
      exact this.symm
    obtain ⟨u, hu⟩ := (hfg _).1 h1
    refine ⟨Representation.Coinvariants.mk ρ u, ?_⟩
    rw [Representation.Coinvariants.map_mk, hu, Representation.Coinvariants.mk_eq_iff, ← neg_sub]
    exact Submodule.neg_mem _ (coinvariantsKer_le_ker σ K (sub_fixedProj_mem hσ hKc hKo w))
  · rintro ⟨u, hu⟩
    obtain ⟨u, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
    rw [Representation.Coinvariants.map_mk] at hu
    rw [← Representation.Coinvariants.map_mk g w, ← hu, Representation.Coinvariants.map_mk,
      (hfg _).2 ⟨u, rfl⟩, map_zero]
end GroundTheory.Automorphic
