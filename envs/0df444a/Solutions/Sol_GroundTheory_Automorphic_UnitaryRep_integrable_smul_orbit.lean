-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrable_smul_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:01:20.952994+00:00
-- url     : https://prove2.me/submissions/d69f2c7f-ccd9-4ca5-b814-a803de2fa78d

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
theorem _root_.solution [SecondCountableTopologyEither G H] (f : G →₁[μ] ℂ) (v : H) :
    Integrable (fun g => f g • π g v) μ :=
  (L1.integrable_coeFn f).smul_bdd ‖v‖ (π.continuous_orbit v).aestronglyMeasurable
    (Eventually.of_forall fun g => (π.norm_map g v).le)
end GroundTheory.Automorphic.UnitaryRep
