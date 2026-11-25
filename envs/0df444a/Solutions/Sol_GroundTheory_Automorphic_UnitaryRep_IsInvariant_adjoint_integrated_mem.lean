-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.adjoint_integrated_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:13.526518+00:00
-- url     : https://prove2.me/submissions/31b2f575-a600-4a73-8b7e-bab27dc17a15

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_integrated_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_orthogonal


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
namespace IsInvariant
theorem _root_.solution {V : Submodule ℂ H} (hcl : IsClosed (V : Set H))
    (hV : π.IsInvariant V) (f : G →₁[μ] ℂ) {v : H} (hv : v ∈ V) :
    adjoint (π.integrated μ f) v ∈ V := by
  have : CompleteSpace V := hcl.completeSpace_coe
  rw [← Submodule.orthogonal_orthogonal V, Submodule.mem_orthogonal]
  intro u hu
  rw [adjoint_inner_right]
  have hu' : π.integrated μ f u ∈ Vᗮ :=
    IsInvariant.integrated_mem π μ (Submodule.isClosed_orthogonal V) hV.orthogonal f hu
  exact (Submodule.mem_orthogonal' _ _).1 hu' v hv
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep
