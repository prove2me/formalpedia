-- Prove2me | solution 1 for GlobalTheory.CentralIdemIntegral.card_mul_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:09.756948+00:00
-- url     : https://prove2.me/submissions/429db6df-345e-4e3d-a50b-62d81530441f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
import Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_card_mul_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CentralIdemIntegral
namespace GlobalTheory.CentralIdemIntegral
theorem _root_.solution :
    ∀ (G O K : Type) [Group G] [Fintype G] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field K] [CharZero K] [Algebra O K] [IsFractionRing O K] (e : MonoidAlgebra K G), e * e = e → (∀ x, e * x = x * e) → ∀ g, ∃ c : O, algebraMap O K c = (Fintype.card G : K) * e.coeff g := by
  intro G O K _ _ _ _ _ _ _ _ _ e he hc g
  exact (IsIntegrallyClosed.isIntegral_iff (R := O)).1
    (isIntegral_card_mul_coeff e he hc g).tower_top
end GlobalTheory.CentralIdemIntegral
