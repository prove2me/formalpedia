-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock02048
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:34:16.650729+00:00
-- url     : https://prove2.me/submissions/14b1b144-1211-4cae-ad1c-e3b567fb4922

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked2048 : pass nodeFast 2048 128 = true := by decide +kernel

private theorem checked2176 : pass nodeFast 2176 128 = true := by decide +kernel

private theorem checked2304 : pass nodeFast 2304 128 = true := by decide +kernel

private theorem checked2432 : pass nodeFast 2432 128 = true := by decide +kernel

private theorem checked2560 : pass nodeFast 2560 128 = true := by decide +kernel

private theorem checked2688 : pass nodeFast 2688 128 = true := by decide +kernel

private theorem checked2816 : pass nodeFast 2816 128 = true := by decide +kernel

private theorem checked2944 : pass nodeFast 2944 128 = true := by decide +kernel

private theorem checked3072 : pass nodeFast 3072 128 = true := by decide +kernel

private theorem checked3200 : pass nodeFast 3200 128 = true := by decide +kernel

private theorem checked3328 : pass nodeFast 3328 128 = true := by decide +kernel

private theorem checked3456 : pass nodeFast 3456 128 = true := by decide +kernel

private theorem checked3584 : pass nodeFast 3584 128 = true := by decide +kernel

private theorem checked3712 : pass nodeFast 3712 128 = true := by decide +kernel

private theorem checked3840 : pass nodeFast 3840 128 = true := by decide +kernel

private theorem checked3968 : pass nodeFast 3968 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 2048 ≤ n → n < 4096 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h2048 : n < 2176
  · exact in_checked_range checked2048 (by omega) (by omega)

  by_cases h2176 : n < 2304
  · exact in_checked_range checked2176 (by omega) (by omega)

  by_cases h2304 : n < 2432
  · exact in_checked_range checked2304 (by omega) (by omega)

  by_cases h2432 : n < 2560
  · exact in_checked_range checked2432 (by omega) (by omega)

  by_cases h2560 : n < 2688
  · exact in_checked_range checked2560 (by omega) (by omega)

  by_cases h2688 : n < 2816
  · exact in_checked_range checked2688 (by omega) (by omega)

  by_cases h2816 : n < 2944
  · exact in_checked_range checked2816 (by omega) (by omega)

  by_cases h2944 : n < 3072
  · exact in_checked_range checked2944 (by omega) (by omega)

  by_cases h3072 : n < 3200
  · exact in_checked_range checked3072 (by omega) (by omega)

  by_cases h3200 : n < 3328
  · exact in_checked_range checked3200 (by omega) (by omega)

  by_cases h3328 : n < 3456
  · exact in_checked_range checked3328 (by omega) (by omega)

  by_cases h3456 : n < 3584
  · exact in_checked_range checked3456 (by omega) (by omega)

  by_cases h3584 : n < 3712
  · exact in_checked_range checked3584 (by omega) (by omega)

  by_cases h3712 : n < 3840
  · exact in_checked_range checked3712 (by omega) (by omega)

  by_cases h3840 : n < 3968
  · exact in_checked_range checked3840 (by omega) (by omega)

  exact in_checked_range checked3968 (by omega) (by omega)
