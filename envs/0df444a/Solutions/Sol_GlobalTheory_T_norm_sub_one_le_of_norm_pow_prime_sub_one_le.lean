-- Prove2me | solution 1 for GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:16.239746+00:00
-- url     : https://prove2.me/submissions/4e7abaf5-3dfa-4868-904f-ca954b53336c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixNearOnePowPrimeDeep
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixNearOnePowPrimeDeepStatement
import Theorems.Thm_GlobalTheory_matrix_near_one_pow_prime_deep


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) → (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) → ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.matrix_near_one_pow_prime_deep | exact GlobalTheory.matrix_near_one_pow_prime_deep | (intros; apply GlobalTheory.matrix_near_one_pow_prime_deep <;> assumption)
end _root_.GlobalTheory.T
