-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.norm_integrated_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:19.705801+00:00
-- url     : https://prove2.me/submissions/33c7cbe7-b007-42dc-93a2-27ffd82ec884

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated

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
theorem _root_.solution (f : G →₁[μ] ℂ) (v : H) :
    ‖π.integrated μ f v‖ ≤ ‖f‖ * ‖v‖ :=
  π.norm_integratedOp_apply_le μ f v
end GroundTheory.Automorphic.UnitaryRep
