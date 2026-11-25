-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.finiteReduction_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:08.584727+00:00
-- url     : https://prove2.me/submissions/525ed57e-636d-4ac5-afdc-6c6048147c31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_finite_quotient_of_pow_le
import Theorems.Thm_GlobalTheory_FormalIsogeny_exists_pow_le_of_finite_quotient

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
variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]
variable [IsLocalRing R]
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {f : τ → MvPowerSeries σ R} : FiniteReduction f ↔
    ∃ N, Ideal.span (Set.range X) ^ N ≤
      Ideal.span (Set.range fun j => MvPowerSeries.map (residue R) (f j)) :=
  ⟨exists_pow_le_of_finite_quotient, fun ⟨_, h⟩ => finite_quotient_of_pow_le h⟩
end GlobalTheory.FormalIsogeny
