-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedProj_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:54.592638+00:00
-- url     : https://prove2.me/submissions/94f7600d-27c9-412e-b4c1-bf4df15071db

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_of_mem_coinvariantsKer
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
theorem _root_.solution {v : V} {w : fixedVectors ρ K} :
    fixedProj ρ hρ hKc hKo v = w ↔ v - w ∈ coinvariantsKer ρ K := by
  constructor
  · rintro rfl
    exact sub_fixedProj_mem hρ hKc hKo v
  · intro h
    have h1 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo h
    rw [map_sub] at h1
    rw [sub_eq_zero.1 h1]
    exact Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2)
end GroundTheory.Automorphic
