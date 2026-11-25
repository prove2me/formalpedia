-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.Equiv.isTraceClass_integrated_and_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:05:39.267612+00:00
-- url     : https://prove2.me/submissions/a507392f-e215-421e-96ca-fd809d90aa92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Theorems.Thm_GroundTheory_Automorphic_isTraceClass_and_trace_eq_of_conj
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_Equiv_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_intertwiners


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
variable {μ : Measure G} {σ : UnitaryRep G K} {τ : UnitaryRep G L}
namespace GroundTheory.Automorphic.UnitaryRep
namespace Equiv
theorem _root_.solution (e : σ.Equiv τ) (f : G →₁[μ] ℂ)
    (h : IsTraceClass (σ.integrated μ f)) :
    IsTraceClass (τ.integrated μ f) ∧ trace (τ.integrated μ f) = trace (σ.integrated μ f) := by
  refine isTraceClass_and_trace_eq_of_conj e.toLinearIsometryEquiv h fun v => ?_
  have := comp_integrated_of_mem_intertwiners σ μ e.mem_intertwiners f
  exact (congrArg (fun T : K →L[ℂ] L => T v) this).symm
end Equiv
end GroundTheory.Automorphic.UnitaryRep
