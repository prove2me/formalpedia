-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.integrated_ccToL1_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:33:31.574971+00:00
-- url     : https://prove2.me/submissions/2262069b-3295-4b2d-9207-9b4707248ae5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_integrated_toLp_apply


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
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (f : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π.integrated μ (ccToL1 μ f) v = ∫ g, f g • π g v ∂μ :=
  π.integrated_toLp_apply μ f v
end GroundTheory.Automorphic.UnitaryRep
