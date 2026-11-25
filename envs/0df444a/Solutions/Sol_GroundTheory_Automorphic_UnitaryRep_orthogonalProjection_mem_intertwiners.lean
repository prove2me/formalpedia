-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:28:17.113314+00:00
-- url     : https://prove2.me/submissions/f89a3446-8865-4eb3-b05c-c82e6518664e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_Equiv_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_iff_commute_starProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_intertwiners
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (j : J) :
    ((V j).orthogonalProjectionOnto : H →L[ℂ] V j) ∈ π.intertwiners (π.restrict (V j) (hinv j)) := by
  rw [mem_intertwiners]
  intro g v
  apply Subtype.ext
  have h := ((isInvariant_iff_commute_starProjection (V j)).1 (hinv j) g).eq
  have h2 : (π g) ((V j).starProjection v) = (V j).starProjection (π g v) :=
    congrArg (fun T : H →L[ℂ] H => T v) h
  rw [coe_restrict_apply, ← Submodule.starProjection_apply, ← Submodule.starProjection_apply]
  exact h2.symm
end GroundTheory.Automorphic.UnitaryRep
