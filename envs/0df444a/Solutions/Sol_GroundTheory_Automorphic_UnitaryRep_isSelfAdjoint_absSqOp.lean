-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.isSelfAdjoint_absSqOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:37.47105+00:00
-- url     : https://prove2.me/submissions/38872c64-fe2f-4033-b216-aec7b54eccff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract

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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (f : G →₁[μ] ℂ) : IsSelfAdjoint (π.absSqOp μ f) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', absSqOp, adjoint_comp, adjoint_adjoint]
end GroundTheory.Automorphic.UnitaryRep
