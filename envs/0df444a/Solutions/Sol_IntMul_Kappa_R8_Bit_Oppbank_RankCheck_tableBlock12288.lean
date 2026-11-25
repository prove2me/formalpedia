-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock12288
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:40:39.001879+00:00
-- url     : https://prove2.me/submissions/e22930a9-42f4-4b12-bc53-a0c03f23aff6

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked12288 : pass nodeFast 12288 128 = true := by decide +kernel

private theorem checked12416 : pass nodeFast 12416 128 = true := by decide +kernel

private theorem checked12544 : pass nodeFast 12544 128 = true := by decide +kernel

private theorem checked12672 : pass nodeFast 12672 128 = true := by decide +kernel

private theorem checked12800 : pass nodeFast 12800 128 = true := by decide +kernel

private theorem checked12928 : pass nodeFast 12928 128 = true := by decide +kernel

private theorem checked13056 : pass nodeFast 13056 128 = true := by decide +kernel

private theorem checked13184 : pass nodeFast 13184 128 = true := by decide +kernel

private theorem checked13312 : pass nodeFast 13312 128 = true := by decide +kernel

private theorem checked13440 : pass nodeFast 13440 128 = true := by decide +kernel

private theorem checked13568 : pass nodeFast 13568 128 = true := by decide +kernel

private theorem checked13696 : pass nodeFast 13696 128 = true := by decide +kernel

private theorem checked13824 : pass nodeFast 13824 128 = true := by decide +kernel

private theorem checked13952 : pass nodeFast 13952 128 = true := by decide +kernel

private theorem checked14080 : pass nodeFast 14080 128 = true := by decide +kernel

private theorem checked14208 : pass nodeFast 14208 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 12288 ≤ n → n < 14336 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h12288 : n < 12416
  · exact in_checked_range checked12288 (by omega) (by omega)

  by_cases h12416 : n < 12544
  · exact in_checked_range checked12416 (by omega) (by omega)

  by_cases h12544 : n < 12672
  · exact in_checked_range checked12544 (by omega) (by omega)

  by_cases h12672 : n < 12800
  · exact in_checked_range checked12672 (by omega) (by omega)

  by_cases h12800 : n < 12928
  · exact in_checked_range checked12800 (by omega) (by omega)

  by_cases h12928 : n < 13056
  · exact in_checked_range checked12928 (by omega) (by omega)

  by_cases h13056 : n < 13184
  · exact in_checked_range checked13056 (by omega) (by omega)

  by_cases h13184 : n < 13312
  · exact in_checked_range checked13184 (by omega) (by omega)

  by_cases h13312 : n < 13440
  · exact in_checked_range checked13312 (by omega) (by omega)

  by_cases h13440 : n < 13568
  · exact in_checked_range checked13440 (by omega) (by omega)

  by_cases h13568 : n < 13696
  · exact in_checked_range checked13568 (by omega) (by omega)

  by_cases h13696 : n < 13824
  · exact in_checked_range checked13696 (by omega) (by omega)

  by_cases h13824 : n < 13952
  · exact in_checked_range checked13824 (by omega) (by omega)

  by_cases h13952 : n < 14080
  · exact in_checked_range checked13952 (by omega) (by omega)

  by_cases h14080 : n < 14208
  · exact in_checked_range checked14080 (by omega) (by omega)

  exact in_checked_range checked14208 (by omega) (by omega)
