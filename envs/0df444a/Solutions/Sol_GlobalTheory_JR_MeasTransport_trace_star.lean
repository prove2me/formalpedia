-- Prove2me | solution 1 for GlobalTheory.JR.MeasTransport.trace_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:01:27.941143+00:00
-- url     : https://prove2.me/submissions/af099462-a547-4d04-ada8-774e1c27e24f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.MeasTransport
theorem _root_.solution [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z
end GlobalTheory.JR.MeasTransport
