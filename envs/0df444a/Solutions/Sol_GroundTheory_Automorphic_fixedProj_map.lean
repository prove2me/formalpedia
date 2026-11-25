-- Prove2me | solution 1 for GroundTheory.Automorphic.fixedProj_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:25.562565+00:00
-- url     : https://prove2.me/submissions/6a6df49b-d996-4475-bfa0-c37082086450

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StabilizerOf
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Theorems.Thm_GroundTheory_Automorphic_map_coinvariantsKer_le
import Theorems.Thm_GroundTheory_Automorphic_coe_fixedMap_apply
import Theorems.Thm_GroundTheory_Automorphic_sub_fixedProj_mem
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_eq_iff

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
omit hρ
namespace GroundTheory.Automorphic
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) (f : Representation.IntertwiningMap ρ σ) (v : V) :
    fixedProj σ hσ hKc hKo (f v) = fixedMap ρ f K (fixedProj ρ hρ hKc hKo v) := by
  rw [fixedProj_eq_iff, coe_fixedMap_apply, ← map_sub]
  exact map_coinvariantsKer_le ρ f K (sub_fixedProj_mem hρ hKc hKo v)
end GroundTheory.Automorphic
