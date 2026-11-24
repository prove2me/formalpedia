-- Prove2me | solution 1 for GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:26.644858+00:00
-- url     : https://prove2.me/submissions/9e336ca9-397d-4bce-bb33-b7e9df97dc02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubDvdChoosePrimePowOfLtStatement
import Theorems.Thm_GlobalTheory_pow_sub_dvd_choose_prime_pow_of_lt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  first | exact @GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | exact GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt | (intros; apply GlobalTheory.pow_sub_dvd_choose_prime_pow_of_lt <;> assumption)
end _root_.GlobalTheory.T
