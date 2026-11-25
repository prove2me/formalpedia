-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.inner_absSqOp_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:45:24.095309+00:00
-- url     : https://prove2.me/submissions/f70227a9-38fc-4a1b-8b26-cd5c60d2f631

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
theorem _root_.solution (f : G →₁[μ] ℂ) (v : H) :
    ⟪v, π.absSqOp μ f v⟫_ℂ = ⟪π.integrated μ f v, π.integrated μ f v⟫_ℂ := by
  rw [absSqOp, comp_apply, adjoint_inner_right]
end GroundTheory.Automorphic.UnitaryRep
