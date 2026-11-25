-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.comp_absSqOp_of_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:17.544792+00:00
-- url     : https://prove2.me/submissions/459b5cf3-eb89-441c-b00a-80266692aaf3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_adjoint_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
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
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {σ : UnitaryRep G K} {T : K →L[ℂ] H}
    (hT : T ∈ σ.intertwiners π) (f : G →₁[μ] ℂ) :
    T ∘L σ.absSqOp μ f = π.absSqOp μ f ∘L T := by
  have h1 := σ.comp_integrated_of_mem_intertwiners μ hT f
  have h2 := π.comp_integrated_of_mem_intertwiners μ (adjoint_mem_intertwiners hT) f
  have h3 : adjoint (π.integrated μ f) ∘L T = T ∘L adjoint (σ.integrated μ f) := by
    have := congrArg adjoint h2
    simpa only [adjoint_comp, adjoint_adjoint] using this
  simp only [absSqOp]
  rw [← ContinuousLinearMap.comp_assoc, ← h3, ContinuousLinearMap.comp_assoc, h1,
    ContinuousLinearMap.comp_assoc]
end GroundTheory.Automorphic.UnitaryRep
