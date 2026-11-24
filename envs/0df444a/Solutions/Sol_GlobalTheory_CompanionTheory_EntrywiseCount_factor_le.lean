-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EntrywiseCount.factor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:19.532914+00:00
-- url     : https://prove2.me/submissions/2afb2119-6daf-40a1-aaad-cdc21f5049a9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe

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
theorem _root_.solution (d : ℕ) (C β t : ℝ) (p : Prop) [Decidable p]
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ (C * (1 + β) ^ d) * (if p then Real.exp ((d : ℝ) * t) else 1) := by
  have hE : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hbase : 1 + β * (if p then Real.exp t else 1)
      ≤ (1 + β) * (if p then Real.exp t else 1) := by
    split_ifs
    · nlinarith
    · linarith
  have hnn : 0 ≤ 1 + β * (if p then Real.exp t else 1) := by
    split_ifs <;> positivity
  have hpow := pow_le_pow_left₀ hnn hbase d
  rw [mul_pow] at hpow
  have hE' : (if p then Real.exp t else 1) ^ d = (if p then Real.exp ((d : ℝ) * t) else 1) := by
    split_ifs
    · rw [← Real.exp_nat_mul]
    · simp
  rw [hE'] at hpow
  calc C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ C * ((1 + β) ^ d * (if p then Real.exp ((d : ℝ) * t) else 1)) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = _ := by ring
end GlobalTheory.CompanionTheory.EntrywiseCount
