-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.comp_integrated_of_mem_intertwiners
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:49.96852+00:00
-- url     : https://prove2.me/submissions/f3aef8b7-06a6-4007-9af3-c85bc64d9817

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_integrated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {σ : UnitaryRep G K} {T : H →L[ℂ] K}
    (hT : T ∈ π.intertwiners σ) (f : G →₁[μ] ℂ) :
    T ∘L π.integrated μ f = σ.integrated μ f ∘L T := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [comp_apply, comp_apply, ← adjoint_inner_left, inner_integrated, inner_integrated]
  congr 1; ext g
  rw [adjoint_inner_left, hT]
end GroundTheory.Automorphic.UnitaryRep
