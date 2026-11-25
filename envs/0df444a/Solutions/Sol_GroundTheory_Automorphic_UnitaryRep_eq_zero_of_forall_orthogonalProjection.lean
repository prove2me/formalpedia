-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.eq_zero_of_forall_orthogonalProjection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:41.708178+00:00
-- url     : https://prove2.me/submissions/2c147685-f1e5-4f6e-847a-217057ad2d39

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_top_le_topologicalClosure_iSup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {x : H}
    (hx : ∀ j, (V j).orthogonalProjectionOnto x = 0) : x = 0 := by
  have hle : (⨆ j, V j) ≤ (ℂ ∙ x)ᗮ := by
    refine iSup_le fun j u hu => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := (Submodule.orthogonalProjectionOnto_eq_zero_iff).1 (hx j)
    rw [Submodule.mem_orthogonal] at this
    rw [← inner_conj_symm, this u hu, map_zero]
  have hcl : (⨆ j, V j).topologicalClosure ≤ (ℂ ∙ x)ᗮ :=
    Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
  have hmem : x ∈ (ℂ ∙ x)ᗮ := hcl (top_le_topologicalClosure_iSup hsum Submodule.mem_top)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  exact inner_self_eq_zero.1 hmem
end GroundTheory.Automorphic.UnitaryRep
