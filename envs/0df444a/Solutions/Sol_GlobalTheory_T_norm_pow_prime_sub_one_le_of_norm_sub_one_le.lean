-- Prove2me | solution 1 for GlobalTheory.T.norm_pow_prime_sub_one_le_of_norm_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:15.438084+00:00
-- url     : https://prove2.me/submissions/b3c96d71-85a3-4f5d-89db-04bb71d933ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowPrimeSubOneNormLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowPrimeSubOneNormLeStatement
import Theorems.Thm_GlobalTheory_pow_prime_sub_one_norm_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
  first | exact @GlobalTheory.pow_prime_sub_one_norm_le | exact GlobalTheory.pow_prime_sub_one_norm_le | (intros; apply GlobalTheory.pow_prime_sub_one_norm_le <;> assumption)
end _root_.GlobalTheory.T
