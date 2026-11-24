-- Prove2me | solution 1 for GlobalTheory.T.pow_prime_range_eq_iterated_difference
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:09.86778+00:00
-- url     : https://prove2.me/submissions/c0b324a5-0c69-4dde-bbe7-b42e0492517e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifference
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowPrimeRangeEqIteratedDifferenceStatement
import Theorems.Thm_GlobalTheory_CNorm_pows_eq_range_dif_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (M : Type) [CommGroup M] (τ : M →* M) (lam : Monoid.End M), p.Prime → (∀ a, lam a = τ a / a) → (∀ a, nrm τ p a = 1) → pows p (⊤ : Subgroup M) = MonoidHom.range (lam ^ (p - 1) : Monoid.End M) ∧ ∀ a : M, a ^ p = 1 ↔ (lam ^ (p - 1) : Monoid.End M) a = 1 := by
  first | exact @GlobalTheory.CNorm.pows_eq_range_dif_pow | exact GlobalTheory.CNorm.pows_eq_range_dif_pow | (intros; apply GlobalTheory.CNorm.pows_eq_range_dif_pow <;> assumption)
end _root_.GlobalTheory.T
