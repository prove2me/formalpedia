-- Prove2me | solution 1 for GroundTheory.Automorphic.eq_of_invariant_of_eqOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:37.17427+00:00
-- url     : https://prove2.me/submissions/7974ad86-4b32-4fd1-b171-173ca8374cf9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsKer_le_ker_of_invariant
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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
variable {ρ} {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] {f g : V →ₗ[ℂ] W}
    (hf : ∀ k ∈ K, ∀ v, f (ρ k v) = f v) (hg : ∀ k ∈ K, ∀ v, g (ρ k v) = g v)
    (h : ∀ v ∈ fixedVectors ρ K, f v = g v) : f = g := by
  ext v
  have hs := sub_fixedProj_mem hρ hKc hKo v
  have e1 : f v = f (fixedProj ρ hρ hKc hKo v) := by
    rw [← sub_eq_zero, ← map_sub]; exact coinvariantsKer_le_ker_of_invariant hf hs
  have e2 : g v = g (fixedProj ρ hρ hKc hKo v) := by
    rw [← sub_eq_zero, ← map_sub]; exact coinvariantsKer_le_ker_of_invariant hg hs
  rw [e1, e2, h _ (fixedProj ρ hρ hKc hKo v).2]
end GroundTheory.Automorphic
