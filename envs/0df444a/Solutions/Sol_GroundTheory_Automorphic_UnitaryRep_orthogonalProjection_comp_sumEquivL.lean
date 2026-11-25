-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_comp_sumEquivL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:56.420816+00:00
-- url     : https://prove2.me/submissions/ad84d27e-a216-4e4c-8490-4da16ac65f34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_coe_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
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
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
variable {σ : UnitaryRep G K}
open Classical
include hsum
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [Fintype (EquivSummands hinv σ)]
    (c : EquivSummands hinv σ → ℂ) (j : J) (k : K) :
    (V j).orthogonalProjectionOnto (sumEquivL hinv c k) =
      if h : (π.restrict (V j) (hinv j)).IsEquivalent σ then
        c ⟨j, h⟩ • summandEquivL hinv ⟨j, h⟩ k else 0 := by
  classical
  simp only [sumEquivL, sum_apply, smul_apply, comp_apply, map_sum, map_smul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp [Submodule.subtypeL_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    · intro w _ hw
      have hwj : j ≠ w.1 := fun e => hw (Subtype.ext e.symm)
      rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun w _ => ?_
    have hwj : j ≠ w.1 := fun e => h (e ▸ w.2)
    rw [Submodule.subtypeL_apply, orthogonalProjection_coe_eq_zero hsum hwj, smul_zero]
end GroundTheory.Automorphic.UnitaryRep
