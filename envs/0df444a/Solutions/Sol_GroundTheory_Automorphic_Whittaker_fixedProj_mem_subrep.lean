-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.fixedProj_mem_subrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:44.638779+00:00
-- url     : https://prove2.me/submissions/658a5eda-7df8-479e-8bea-1a1f1bcf0ea1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isSmooth_subrep
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
open GroundTheory.Automorphic.Whittaker
open Set Filter Topology MeasureTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hρ : IsSmooth ρ) (W : Subrepresentation ρ) {K : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) {x : V} (hx : x ∈ W) :
    ((fixedProj ρ hρ hKc hKo x : fixedVectors ρ K) : V) ∈ W := by
  let ι : Representation.IntertwiningMap (V := W.toSubmodule) W.toRepresentation ρ :=
    ⟨W.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have key := fixedProj_map hKc hKo (isSmooth_subrep hρ W) hρ ι ⟨x, hx⟩
  have e : ((fixedProj ρ hρ hKc hKo x : fixedVectors ρ K) : V) =
      (((fixedProj (V := W.toSubmodule) W.toRepresentation (isSmooth_subrep hρ W) hKc hKo ⟨x, hx⟩ :
        fixedVectors _ K) : W.toSubmodule) : V) :=
    congrArg Subtype.val key
  rw [e]
  exact Subtype.property _
end GroundTheory.Automorphic.Whittaker
