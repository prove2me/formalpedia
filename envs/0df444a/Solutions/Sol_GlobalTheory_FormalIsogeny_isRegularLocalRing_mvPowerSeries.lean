-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:22.861925+00:00
-- url     : https://prove2.me/submissions/74cd8717-46d3-4552-af48-97e595887bb9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Theorems.Thm_GlobalTheory_FormalIsogeny_isRegularLocalRing_powerSeries

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
theorem _root_.solution (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (σ : Type*) [Finite σ] : IsRegularLocalRing (MvPowerSeries σ R) := by
  have : ∀ n, IsRegularLocalRing (MvPowerSeries (Fin n) R) := fun n => by
    induction n with
    | zero => exact IsRegularLocalRing.of_ringEquiv (isEmptyEquiv (Fin 0) R).toRingEquiv.symm
    | succ n ih =>
      have := isRegularLocalRing_powerSeries (MvPowerSeries (Fin n) R)
      exact IsRegularLocalRing.of_ringEquiv (finSuccEquiv R n).toRingEquiv.symm
  have := this (Nat.card σ)
  exact IsRegularLocalRing.of_ringEquiv (renameEquiv R (Finite.equivFin σ)).toRingEquiv.symm
end GlobalTheory.FormalIsogeny
