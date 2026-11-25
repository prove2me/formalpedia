-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.hasSum_trace_integrated_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:08:32.972373+00:00
-- url     : https://prove2.me/submissions/5dcbebbb-8d4a-415a-8738-1b6830a33da9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isTraceClass_integrated_restrict
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_collectedHilbertBasis_apply
import Theorems.Thm_GroundTheory_Automorphic_IsTraceClass_hasSum_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace InnerProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (π : UnitaryRep G H) (μ : Measure G) (f : G →₁[μ] ℂ)
variable {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable {π μ f}
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
include hsum
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (hT : IsTraceClass (π.integrated μ f)) :
    HasSum (fun j => trace ((π.restrict (V j) (hinv j)).integrated μ f))
      (trace (π.integrated μ f)) := by
  have h1 := hT.hasSum_trace (collectedHilbertBasis hsum)
  refine h1.sigma fun j => ?_
  refine ((isTraceClass_integrated_restrict hinv hT j).hasSum_trace
    (stdHilbertBasis ℂ (V j))).congr_fun fun i => ?_
  rw [collectedHilbertBasis_apply, ← integrated_restrict_apply π μ f hinv j]
  rfl
end GroundTheory.Automorphic.UnitaryRep
