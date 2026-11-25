-- Prove2me | solution 1 for GlobalTheory.DiscEval.isClosed_fieldRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:03:18.84672+00:00
-- url     : https://prove2.me/submissions/1ba7f4a9-9c7a-4840-99a0-b108a3414c38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscEval
open Filter Topology IsLocalRing
open scoped PowerSeries LaurentSeries
variable (p : ℕ) [Fact p.Prime]
variable {p}
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory.DiscEval
theorem _root_.solution : IsClosed ((fieldEmb L).fieldRange : Set ℂ_[p]) :=
  (LinearMap.range ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp
    L.val).toLinearMap).closed_of_finiteDimensional
end GlobalTheory.DiscEval
