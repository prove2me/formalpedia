-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.top_le_topologicalClosure_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:28:33.736886+00:00
-- url     : https://prove2.me/submissions/f3da94c8-f134-405c-8851-67178c9d9118

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_DirectSum
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_directSum_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.directSum_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open scoped InnerProductSpace
open ContinuousLinearMap Submodule
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable {π : UnitaryRep G H}
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution
    (hV : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ) :
    ⊤ ≤ (⨆ j, V j).topologicalClosure := by
  have h1 : LinearMap.range hV.OrthogonalFamily.linearIsometry.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hV.surjective_isometry
  rw [hV.OrthogonalFamily.range_linearIsometry] at h1
  simpa [Submodule.subtypeₗᵢ_toLinearMap, Submodule.range_subtype] using h1.ge
end GroundTheory.Automorphic.UnitaryRep
