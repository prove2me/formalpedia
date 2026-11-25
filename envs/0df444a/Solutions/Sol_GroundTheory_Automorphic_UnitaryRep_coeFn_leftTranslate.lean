-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.coeFn_leftTranslate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:16.332807+00:00
-- url     : https://prove2.me/submissions/3fb7bb26-8e4a-4f8d-be5e-e73524e273d0

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
variable [IsTopologicalGroup G] [BorelSpace G]
omit [OpensMeasurableSpace G]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution [μ.IsMulLeftInvariant] (h : G) (f : G →₁[μ] ℂ) :
    (leftTranslate μ h f : G → ℂ) =ᵐ[μ] fun g => f (h⁻¹ * g) :=
  Lp.coeFn_compMeasurePreserving _ _
end GroundTheory.Automorphic.UnitaryRep
