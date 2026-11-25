-- Prove2me | solution 1 for GlobalTheory.BadShare.sum_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:54.231801+00:00
-- url     : https://prove2.me/submissions/1d45ef2a-e1bb-4a7b-a8f2-81ca5a9b7c6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardIrreducibleSamePrimeToPartRootsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassSamePartOneFactorLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 8) (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 N, (d : ℝ) * u ^ d ≤ 6 * u ^ 2 := by
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ Finset.range (N + 1 - 2), ((2 + k : ℕ) : ℝ) * u ^ (2 + k)
      ≤ ∑ k ∈ Finset.range (N + 1 - 2), 3 * u ^ 2 * (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k _
        have hk : ((2 + k : ℕ) : ℝ) ≤ 3 * 4 ^ k := by
          have h1 : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
          have h2 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
          exact_mod_cast (by omega : 2 + k ≤ 3 * 4 ^ k)
        have hu : u ^ k ≤ (1 / 8 : ℝ) ^ k := pow_le_pow_left₀ h0 h1 k
        calc ((2 + k : ℕ) : ℝ) * u ^ (2 + k) = ((2 + k : ℕ) : ℝ) * u ^ k * u ^ 2 := by ring
          _ ≤ (3 * 4 ^ k) * (1 / 8 : ℝ) ^ k * u ^ 2 := by gcongr
          _ = 3 * u ^ 2 * (1 / 2 : ℝ) ^ k := by
            rw [show (1 / 2 : ℝ) = 4 * (1 / 8) by norm_num, mul_pow]
            ring
    _ = 3 * u ^ 2 * ∑ k ∈ Finset.range (N + 1 - 2), (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ 3 * u ^ 2 * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ = 6 * u ^ 2 := by ring
end GlobalTheory.BadShare
