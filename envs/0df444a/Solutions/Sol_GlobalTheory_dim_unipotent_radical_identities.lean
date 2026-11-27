-- Prove2me | solution 1 for GlobalTheory.dim_unipotent_radical_identities
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:38:13.622484+00:00
-- url     : https://prove2.me/submissions/fd67f159-9975-4510-bb93-1e03e5435224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqSumEqSumSqAddTwoMulSumLt
import Theorems.Thm_GlobalTheory_sq_sum_eq_sum_sq_add_two_mul_sum_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
open Matrix Finset Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]
end _root_.GlobalTheory
end GlobalTheory
