-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.IsInvariant.absSqOp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:54:20.470876+00:00
-- url     : https://prove2.me/submissions/74678cdc-a0e3-418d-b50c-b6ab3a843c93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_adjoint_integrated_mem
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsInvariant_integrated_mem


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
    π.absSqOp μ f v ∈ V :=
  hV.adjoint_integrated_mem hcl f (IsInvariant.integrated_mem π μ hcl hV f hv)
end IsInvariant
end GroundTheory.Automorphic.UnitaryRep
