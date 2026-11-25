-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock16384
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:40:41.228128+00:00
-- url     : https://prove2.me/submissions/782dcfe2-f01c-4eae-b694-f8c321487ef9

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked16384 : pass nodeFast 16384 128 = true := by decide +kernel

private theorem checked16512 : pass nodeFast 16512 128 = true := by decide +kernel

private theorem checked16640 : pass nodeFast 16640 128 = true := by decide +kernel

private theorem checked16768 : pass nodeFast 16768 128 = true := by decide +kernel

private theorem checked16896 : pass nodeFast 16896 128 = true := by decide +kernel

private theorem checked17024 : pass nodeFast 17024 128 = true := by decide +kernel

private theorem checked17152 : pass nodeFast 17152 128 = true := by decide +kernel

private theorem checked17280 : pass nodeFast 17280 128 = true := by decide +kernel

private theorem checked17408 : pass nodeFast 17408 128 = true := by decide +kernel

private theorem checked17536 : pass nodeFast 17536 128 = true := by decide +kernel

private theorem checked17664 : pass nodeFast 17664 128 = true := by decide +kernel

private theorem checked17792 : pass nodeFast 17792 128 = true := by decide +kernel

private theorem checked17920 : pass nodeFast 17920 128 = true := by decide +kernel

private theorem checked18048 : pass nodeFast 18048 128 = true := by decide +kernel

private theorem checked18176 : pass nodeFast 18176 128 = true := by decide +kernel

private theorem checked18304 : pass nodeFast 18304 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 16384 ≤ n → n < 18432 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h16384 : n < 16512
  · exact in_checked_range checked16384 (by omega) (by omega)

  by_cases h16512 : n < 16640
  · exact in_checked_range checked16512 (by omega) (by omega)

  by_cases h16640 : n < 16768
  · exact in_checked_range checked16640 (by omega) (by omega)

  by_cases h16768 : n < 16896
  · exact in_checked_range checked16768 (by omega) (by omega)

  by_cases h16896 : n < 17024
  · exact in_checked_range checked16896 (by omega) (by omega)

  by_cases h17024 : n < 17152
  · exact in_checked_range checked17024 (by omega) (by omega)

  by_cases h17152 : n < 17280
  · exact in_checked_range checked17152 (by omega) (by omega)

  by_cases h17280 : n < 17408
  · exact in_checked_range checked17280 (by omega) (by omega)

  by_cases h17408 : n < 17536
  · exact in_checked_range checked17408 (by omega) (by omega)

  by_cases h17536 : n < 17664
  · exact in_checked_range checked17536 (by omega) (by omega)

  by_cases h17664 : n < 17792
  · exact in_checked_range checked17664 (by omega) (by omega)

  by_cases h17792 : n < 17920
  · exact in_checked_range checked17792 (by omega) (by omega)

  by_cases h17920 : n < 18048
  · exact in_checked_range checked17920 (by omega) (by omega)

  by_cases h18048 : n < 18176
  · exact in_checked_range checked18048 (by omega) (by omega)

  by_cases h18176 : n < 18304
  · exact in_checked_range checked18176 (by omega) (by omega)

  exact in_checked_range checked18304 (by omega) (by omega)
