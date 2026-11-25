-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EntrywiseCount.prod_entrywise_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:40:53.719918+00:00
-- url     : https://prove2.me/submissions/545f0f73-3626-4402-99b7-c4346aa2f363

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe
import Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_prod_indicator
import Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_factor_le

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
theorem _root_.solution : ∀ (n r d : ℕ), r ≤ n → ∀ (C β t : ℝ), 0 ≤ C → 0 ≤ β → 0 ≤ t →
    ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n))
        * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) := by
  intro n r d hr C β t hC hβ ht
  have hnn : ∀ (i j : Fin n), 0 ≤
      C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d := by
    intro i j
    have : 0 ≤ (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1) := by
      split_ifs <;> positivity
    positivity
  have step : ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ ∏ i : Fin n, ∏ j : Fin n, ((C * (1 + β) ^ d) *
          (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp ((d : ℝ) * t) else 1)) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.prod_nonneg (fun j _ => hnn i j)
    · intro i _
      apply Finset.prod_le_prod
      · intro j _
        exact hnn i j
      · intro j _
        exact factor_le d C β t _ hC hβ ht
  refine step.trans (le_of_eq ?_)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [prod_indicator n r hr, ← Real.exp_nat_mul, ← pow_mul]
  have hp : (((1 + β) ^ d) ^ n) ^ n = (1 + β) ^ (d * (n * n)) := by
    rw [← pow_mul, ← pow_mul]
  have : (((r * (n - r) : ℕ) : ℝ)) * ((d : ℝ) * t) = (d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t := by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    ring
  rw [this]
  rw [hp]
end GlobalTheory.CompanionTheory.EntrywiseCount
