-- Prove2me | solution 1 for GlobalTheory.DiscEval.finite_residueField_integralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:01:13.273329+00:00
-- url     : https://prove2.me/submissions/c9f1fedc-8ccd-4554-9ac2-041a4d486086

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BasisChangePf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_faithful
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_cl_isLocalHom


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
theorem _root_.solution :
    Finite (ResidueField (integralClosure ℤ_[p] L)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[p] ℚ_[p] L
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[p] L
  have : Finite (ResidueField ℤ_[p]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[p])
end GlobalTheory.DiscEval
