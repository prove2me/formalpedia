-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:55.173164+00:00
-- url     : https://prove2.me/submissions/c92a7268-e0bc-487d-88b1-e280ddcc732a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution [IsLocalRing R] {g : MvPowerSeries σ R} :
    g ∈ maximalIdeal (MvPowerSeries σ R) ↔ constantCoeff g ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]
end GlobalTheory.FormalIsogeny
