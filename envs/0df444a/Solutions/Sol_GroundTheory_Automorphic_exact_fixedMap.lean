-- Prove2me | solution 1 for GroundTheory.Automorphic.exact_fixedMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:06.283448+00:00
-- url     : https://prove2.me/submissions/c2ecd981-2d6f-4434-a062-9b1f9119367a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_coe_fixedMap_apply
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_map

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
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
variable {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
  {ρ} {σ : Representation ℂ G W} {τ : Representation ℂ G X} {K : Subgroup G}
namespace GroundTheory.Automorphic
theorem _root_.solution (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {f : Representation.IntertwiningMap ρ σ}
    {g : Representation.IntertwiningMap σ τ} (hfg : Function.Exact f g) :
    Function.Exact (fixedMap ρ f K) (fixedMap σ g K) := by
  intro y
  constructor
  · intro hy
    have hy' : g (y : W) = 0 := by simpa [Subtype.ext_iff, coe_fixedMap_apply] using hy
    obtain ⟨v, hv⟩ := (hfg (y : W)).1 hy'
    refine ⟨fixedProj ρ hρ hKc hKo v, ?_⟩
    rw [← fixedProj_map hKc hKo hρ hσ f, hv]
    exact Subtype.ext (fixedProj_apply_of_mem hσ hKc hKo y.2)
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    simp only [coe_fixedMap_apply, ZeroMemClass.coe_zero]
    exact (hfg _).2 ⟨x, rfl⟩
end GroundTheory.Automorphic
