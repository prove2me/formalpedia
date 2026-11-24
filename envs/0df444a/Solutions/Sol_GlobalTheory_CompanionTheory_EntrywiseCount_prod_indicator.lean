-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EntrywiseCount.prod_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:59.263801+00:00
-- url     : https://prove2.me/submissions/40389dc7-a527-435a-921d-3627e79df6dd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe
import Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_card_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_card_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EntrywiseCount
namespace GlobalTheory.CompanionTheory.EntrywiseCount
theorem _root_.solution (n r : ℕ) (hr : r ≤ n) (E : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = E ^ (r * (n - r)) := by
  have inner : ∀ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = if (i : ℕ) < r then E ^ (n - r) else 1 := by
    intro i
    by_cases hi : (i : ℕ) < r
    · simp only [hi, true_and, if_true]
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_ge n r hr]
    · simp [hi]
  simp only [inner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_lt n r hr,
    ← pow_mul, mul_comm]
end GlobalTheory.CompanionTheory.EntrywiseCount
