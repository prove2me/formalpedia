-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock06144
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T08:00:32.387806+00:00
-- url     : https://prove2.me/submissions/ea6e41ed-30e7-47c3-adee-1f2f386c9430

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked6144 : pass nodeFast 6144 128 = true := by decide +kernel

private theorem checked6272 : pass nodeFast 6272 128 = true := by decide +kernel

private theorem checked6400 : pass nodeFast 6400 128 = true := by decide +kernel

private theorem checked6528 : pass nodeFast 6528 128 = true := by decide +kernel

private theorem checked6656 : pass nodeFast 6656 128 = true := by decide +kernel

private theorem checked6784 : pass nodeFast 6784 128 = true := by decide +kernel

private theorem checked6912 : pass nodeFast 6912 128 = true := by decide +kernel

private theorem checked7040 : pass nodeFast 7040 128 = true := by decide +kernel

private theorem checked7168 : pass nodeFast 7168 128 = true := by decide +kernel

private theorem checked7296 : pass nodeFast 7296 128 = true := by decide +kernel

private theorem checked7424 : pass nodeFast 7424 128 = true := by decide +kernel

private theorem checked7552 : pass nodeFast 7552 128 = true := by decide +kernel

private theorem checked7680 : pass nodeFast 7680 128 = true := by decide +kernel

private theorem checked7808 : pass nodeFast 7808 128 = true := by decide +kernel

private theorem checked7936 : pass nodeFast 7936 128 = true := by decide +kernel

private theorem checked8064 : pass nodeFast 8064 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 6144 ≤ n → n < 8192 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h6144 : n < 6272
  · exact in_checked_range checked6144 (by omega) (by omega)

  by_cases h6272 : n < 6400
  · exact in_checked_range checked6272 (by omega) (by omega)

  by_cases h6400 : n < 6528
  · exact in_checked_range checked6400 (by omega) (by omega)

  by_cases h6528 : n < 6656
  · exact in_checked_range checked6528 (by omega) (by omega)

  by_cases h6656 : n < 6784
  · exact in_checked_range checked6656 (by omega) (by omega)

  by_cases h6784 : n < 6912
  · exact in_checked_range checked6784 (by omega) (by omega)

  by_cases h6912 : n < 7040
  · exact in_checked_range checked6912 (by omega) (by omega)

  by_cases h7040 : n < 7168
  · exact in_checked_range checked7040 (by omega) (by omega)

  by_cases h7168 : n < 7296
  · exact in_checked_range checked7168 (by omega) (by omega)

  by_cases h7296 : n < 7424
  · exact in_checked_range checked7296 (by omega) (by omega)

  by_cases h7424 : n < 7552
  · exact in_checked_range checked7424 (by omega) (by omega)

  by_cases h7552 : n < 7680
  · exact in_checked_range checked7552 (by omega) (by omega)

  by_cases h7680 : n < 7808
  · exact in_checked_range checked7680 (by omega) (by omega)

  by_cases h7808 : n < 7936
  · exact in_checked_range checked7808 (by omega) (by omega)

  by_cases h7936 : n < 8064
  · exact in_checked_range checked7936 (by omega) (by omega)

  exact in_checked_range checked8064 (by omega) (by omega)
