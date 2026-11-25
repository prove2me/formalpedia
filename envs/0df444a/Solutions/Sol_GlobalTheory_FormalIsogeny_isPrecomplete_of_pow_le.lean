-- Prove2me | solution 1 for GlobalTheory.FormalIsogeny.isPrecomplete_of_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:56.249901+00:00
-- url     : https://prove2.me/submissions/69cfa2f6-a3ba-4a31-9475-1e19e2f912ac

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
namespace GlobalTheory.FormalIsogeny
theorem _root_.solution {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  refine ⟨fun u hu => ?_⟩
  have he' : ∀ n, I ^ ((e + 1) * n) ≤ J ^ n := fun n => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right e.le_succ).trans he) n
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => u ((e + 1) * n)) fun {m n} hmn =>
    (hu (Nat.mul_le_mul_left _ hmn)).mono (Submodule.smul_mono_left (he' m))
  exact ⟨L, fun n => (hu (Nat.le_mul_of_pos_left n e.succ_pos)).trans
    ((hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJ n)))⟩
end GlobalTheory.FormalIsogeny
