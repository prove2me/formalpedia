-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.integrated_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:34.969577+00:00
-- url     : https://prove2.me/submissions/72ae265e-32d6-4109-b605-c889918fae24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_comp_integrated_of_mem_intertwiners
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isInvariant_iff_commute_starProjection
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_mem_intertwiners_self_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply



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
namespace IsInvariant
theorem _root_.solution {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (f : G →₁[μ] ℂ) {v : H} (hv : v ∈ V) :
    π.integrated μ f v ∈ V := by
  have : CompleteSpace V := hcl.completeSpace_coe
  have hP : V.starProjection ∈ π.intertwiners π :=
    mem_intertwiners_self_iff.mpr fun g =>
      ((isInvariant_iff_commute_starProjection V).mp hV g).symm
  have h := congrArg (fun T : H →L[ℂ] H => T v) (π.comp_integrated_of_mem_intertwiners μ hP f)
  simp only [comp_apply, Submodule.starProjection_eq_self_iff.mpr hv] at h
  rw [← h]
  exact V.starProjection_apply_mem _
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep
