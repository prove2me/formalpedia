-- Prove2me | solution 1 for GlobalTheory.valuationRing_exists_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:17.135176+00:00
-- url     : https://prove2.me/submissions/d5a62c9e-743e-4bda-82c3-38889dfb0024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPolynomialMapMaximalIdealIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (c : O) {k : ℕ} (hk : 0 < k) :
    ∃ r : O, r ^ k = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O K c) hk
  have hint : IsIntegral O z := IsIntegral.of_pow hk (hz ▸ isIntegral_algebraMap)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).1 hint
  exact ⟨r, IsFractionRing.injective O K (by rw [map_pow, hz])⟩
end GlobalTheory
