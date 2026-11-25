-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.ringKrullDim_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:02:42.428507+00:00
-- url     : https://prove2.me/submissions/12f10194-f199-4a60-8d03-c2deb8e4648d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim (PowerSeries R) = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ringKrullDim_succ_le_ringKrullDim_powerseries
  have hX : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have h := ringKrullDim_le_ringKrullDim_quotient_add_card
    ({PowerSeries.X} : Finset (PowerSeries R)) (by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      simpa using hX)
  have hker : Ideal.span (({PowerSeries.X} : Finset (PowerSeries R)) : Set (PowerSeries R)) =
      RingHom.ker (PowerSeries.constantCoeff (R := R)) := by
    ext g
    rw [Finset.coe_singleton, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, RingHom.mem_ker]
  have e := (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective
    (f := PowerSeries.constantCoeff (R := R)) fun r => ⟨PowerSeries.C r, PowerSeries.constantCoeff_C r⟩)
  rw [ringKrullDim_eq_of_ringEquiv e] at h
  simpa using h
end GlobalTheory.FormalIsogeny
