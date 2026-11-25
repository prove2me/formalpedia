-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.FiniteReduction.finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:41.556352+00:00
-- url     : https://prove2.me/submissions/8705524a-86c2-4e88-bcd9-6417d0d72ff2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_quotient_of_residue

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
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
namespace GlobalTheory.FormalIsogeny
namespace FiniteReduction
theorem _root_.solution {f : τ → MvPowerSeries σ R} (h : FiniteReduction f) :
    Module.Finite R (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) := by
  refine finite_quotient_of_residue _ ?_
  rw [Ideal.map_span, ← Set.range_comp]
  exact h
end FiniteReduction
end GlobalTheory.FormalIsogeny
