-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.summandEquivL_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:54.112915+00:00
-- url     : https://prove2.me/submissions/5ab4020a-1bb0-4415-97e7-716861077b3d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (hσ : σ.IsIrreducible) (w : EquivSummands hinv σ) :
    summandEquivL hinv w ≠ 0 := by
  have := hσ.1
  obtain ⟨k, hk⟩ := exists_ne (0 : K)
  intro h
  have h1 := congrArg (fun T : K →L[ℂ] V w.1 => T k) h
  simp only [zero_apply] at h1
  apply hk
  have h2 : ‖summandEquivL hinv w k‖ = ‖k‖ := LinearIsometryEquiv.norm_map _ k
  rw [h1, norm_zero] at h2
  exact norm_eq_zero.1 h2.symm
end GroundTheory.Automorphic.UnitaryRep
