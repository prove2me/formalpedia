-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock32768
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T08:00:37.70468+00:00
-- url     : https://prove2.me/submissions/2f86d2ad-1923-4ef4-8778-0968c996eb9e

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked32768 : pass nodeFast 32768 128 = true := by decide +kernel

private theorem checked32896 : pass nodeFast 32896 128 = true := by decide +kernel

private theorem checked33024 : pass nodeFast 33024 128 = true := by decide +kernel

private theorem checked33152 : pass nodeFast 33152 128 = true := by decide +kernel

private theorem checked33280 : pass nodeFast 33280 128 = true := by decide +kernel

private theorem checked33408 : pass nodeFast 33408 128 = true := by decide +kernel

private theorem checked33536 : pass nodeFast 33536 128 = true := by decide +kernel

private theorem checked33664 : pass nodeFast 33664 128 = true := by decide +kernel

private theorem checked33792 : pass nodeFast 33792 128 = true := by decide +kernel

private theorem checked33920 : pass nodeFast 33920 128 = true := by decide +kernel

private theorem checked34048 : pass nodeFast 34048 128 = true := by decide +kernel

private theorem checked34176 : pass nodeFast 34176 128 = true := by decide +kernel

private theorem checked34304 : pass nodeFast 34304 128 = true := by decide +kernel

private theorem checked34432 : pass nodeFast 34432 128 = true := by decide +kernel

private theorem checked34560 : pass nodeFast 34560 128 = true := by decide +kernel

private theorem checked34688 : pass nodeFast 34688 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 32768 ≤ n → n < 34816 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h32768 : n < 32896
  · exact in_checked_range checked32768 (by omega) (by omega)

  by_cases h32896 : n < 33024
  · exact in_checked_range checked32896 (by omega) (by omega)

  by_cases h33024 : n < 33152
  · exact in_checked_range checked33024 (by omega) (by omega)

  by_cases h33152 : n < 33280
  · exact in_checked_range checked33152 (by omega) (by omega)

  by_cases h33280 : n < 33408
  · exact in_checked_range checked33280 (by omega) (by omega)

  by_cases h33408 : n < 33536
  · exact in_checked_range checked33408 (by omega) (by omega)

  by_cases h33536 : n < 33664
  · exact in_checked_range checked33536 (by omega) (by omega)

  by_cases h33664 : n < 33792
  · exact in_checked_range checked33664 (by omega) (by omega)

  by_cases h33792 : n < 33920
  · exact in_checked_range checked33792 (by omega) (by omega)

  by_cases h33920 : n < 34048
  · exact in_checked_range checked33920 (by omega) (by omega)

  by_cases h34048 : n < 34176
  · exact in_checked_range checked34048 (by omega) (by omega)

  by_cases h34176 : n < 34304
  · exact in_checked_range checked34176 (by omega) (by omega)

  by_cases h34304 : n < 34432
  · exact in_checked_range checked34304 (by omega) (by omega)

  by_cases h34432 : n < 34560
  · exact in_checked_range checked34432 (by omega) (by omega)

  by_cases h34560 : n < 34688
  · exact in_checked_range checked34560 (by omega) (by omega)

  exact in_checked_range checked34688 (by omega) (by omega)
