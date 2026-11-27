-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrated_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:14.440914+00:00
-- url     : https://prove2.me/submissions/1b28bcd5-bc67-44c8-b1ef-1bcac0e80844

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_Integrated
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_apply_eq_integral
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrable_smul_orbit

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
theorem _root_.solution [SecondCountableTopologyEither G H] (f : G →₁[μ] ℂ) (v : H) :
    π.integrated μ f v = ∫ g, f g • π g v ∂μ :=
  π.integrated_apply_eq_integral μ f v (π.integrable_smul_orbit μ f v)
end GroundTheory.Automorphic.UnitaryRep
