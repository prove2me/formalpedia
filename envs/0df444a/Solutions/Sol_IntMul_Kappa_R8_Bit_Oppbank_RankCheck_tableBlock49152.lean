-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock49152
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:42:15.375652+00:00
-- url     : https://prove2.me/submissions/1fe9f21c-7aef-424b-85cd-7b60304bf7d4

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked49152 : pass nodeFast 49152 128 = true := by decide +kernel

private theorem checked49280 : pass nodeFast 49280 128 = true := by decide +kernel

private theorem checked49408 : pass nodeFast 49408 128 = true := by decide +kernel

private theorem checked49536 : pass nodeFast 49536 128 = true := by decide +kernel

private theorem checked49664 : pass nodeFast 49664 128 = true := by decide +kernel

private theorem checked49792 : pass nodeFast 49792 128 = true := by decide +kernel

private theorem checked49920 : pass nodeFast 49920 128 = true := by decide +kernel

private theorem checked50048 : pass nodeFast 50048 128 = true := by decide +kernel

private theorem checked50176 : pass nodeFast 50176 128 = true := by decide +kernel

private theorem checked50304 : pass nodeFast 50304 128 = true := by decide +kernel

private theorem checked50432 : pass nodeFast 50432 128 = true := by decide +kernel

private theorem checked50560 : pass nodeFast 50560 128 = true := by decide +kernel

private theorem checked50688 : pass nodeFast 50688 128 = true := by decide +kernel

private theorem checked50816 : pass nodeFast 50816 128 = true := by decide +kernel

private theorem checked50944 : pass nodeFast 50944 128 = true := by decide +kernel

private theorem checked51072 : pass nodeFast 51072 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 49152 ≤ n → n < 51200 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h49152 : n < 49280
  · exact in_checked_range checked49152 (by omega) (by omega)

  by_cases h49280 : n < 49408
  · exact in_checked_range checked49280 (by omega) (by omega)

  by_cases h49408 : n < 49536
  · exact in_checked_range checked49408 (by omega) (by omega)

  by_cases h49536 : n < 49664
  · exact in_checked_range checked49536 (by omega) (by omega)

  by_cases h49664 : n < 49792
  · exact in_checked_range checked49664 (by omega) (by omega)

  by_cases h49792 : n < 49920
  · exact in_checked_range checked49792 (by omega) (by omega)

  by_cases h49920 : n < 50048
  · exact in_checked_range checked49920 (by omega) (by omega)

  by_cases h50048 : n < 50176
  · exact in_checked_range checked50048 (by omega) (by omega)

  by_cases h50176 : n < 50304
  · exact in_checked_range checked50176 (by omega) (by omega)

  by_cases h50304 : n < 50432
  · exact in_checked_range checked50304 (by omega) (by omega)

  by_cases h50432 : n < 50560
  · exact in_checked_range checked50432 (by omega) (by omega)

  by_cases h50560 : n < 50688
  · exact in_checked_range checked50560 (by omega) (by omega)

  by_cases h50688 : n < 50816
  · exact in_checked_range checked50688 (by omega) (by omega)

  by_cases h50816 : n < 50944
  · exact in_checked_range checked50816 (by omega) (by omega)

  by_cases h50944 : n < 51072
  · exact in_checked_range checked50944 (by omega) (by omega)

  exact in_checked_range checked51072 (by omega) (by omega)
