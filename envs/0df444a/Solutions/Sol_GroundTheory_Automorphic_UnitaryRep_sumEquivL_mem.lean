-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.sumEquivL_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:23:57.473325+00:00
-- url     : https://prove2.me/submissions/cd1fbbf6-ed61-404f-a984-dc96a0052b00

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_summandEquivL_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_subtypeL_mem_intertwiners


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
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
variable {σ : UnitaryRep G K}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [Fintype (EquivSummands hinv σ)] (c : EquivSummands hinv σ → ℂ) :
    sumEquivL hinv c ∈ σ.intertwiners π :=
  Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _
    (comp_mem_intertwiners (subtypeL_mem_intertwiners π (V w.1) (hinv w.1))
      (summandEquivL_mem hinv w))
end GroundTheory.Automorphic.UnitaryRep
