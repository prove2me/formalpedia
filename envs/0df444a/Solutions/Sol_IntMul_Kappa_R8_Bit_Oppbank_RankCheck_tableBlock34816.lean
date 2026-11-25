-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock34816
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:40:43.259801+00:00
-- url     : https://prove2.me/submissions/6ebb5189-3b91-4ed0-8965-d5f1edc2e5d0

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked34816 : pass nodeFast 34816 128 = true := by decide +kernel

private theorem checked34944 : pass nodeFast 34944 128 = true := by decide +kernel

private theorem checked35072 : pass nodeFast 35072 128 = true := by decide +kernel

private theorem checked35200 : pass nodeFast 35200 128 = true := by decide +kernel

private theorem checked35328 : pass nodeFast 35328 128 = true := by decide +kernel

private theorem checked35456 : pass nodeFast 35456 128 = true := by decide +kernel

private theorem checked35584 : pass nodeFast 35584 128 = true := by decide +kernel

private theorem checked35712 : pass nodeFast 35712 128 = true := by decide +kernel

private theorem checked35840 : pass nodeFast 35840 128 = true := by decide +kernel

private theorem checked35968 : pass nodeFast 35968 128 = true := by decide +kernel

private theorem checked36096 : pass nodeFast 36096 128 = true := by decide +kernel

private theorem checked36224 : pass nodeFast 36224 128 = true := by decide +kernel

private theorem checked36352 : pass nodeFast 36352 128 = true := by decide +kernel

private theorem checked36480 : pass nodeFast 36480 128 = true := by decide +kernel

private theorem checked36608 : pass nodeFast 36608 128 = true := by decide +kernel

private theorem checked36736 : pass nodeFast 36736 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 34816 ≤ n → n < 36864 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h34816 : n < 34944
  · exact in_checked_range checked34816 (by omega) (by omega)

  by_cases h34944 : n < 35072
  · exact in_checked_range checked34944 (by omega) (by omega)

  by_cases h35072 : n < 35200
  · exact in_checked_range checked35072 (by omega) (by omega)

  by_cases h35200 : n < 35328
  · exact in_checked_range checked35200 (by omega) (by omega)

  by_cases h35328 : n < 35456
  · exact in_checked_range checked35328 (by omega) (by omega)

  by_cases h35456 : n < 35584
  · exact in_checked_range checked35456 (by omega) (by omega)

  by_cases h35584 : n < 35712
  · exact in_checked_range checked35584 (by omega) (by omega)

  by_cases h35712 : n < 35840
  · exact in_checked_range checked35712 (by omega) (by omega)

  by_cases h35840 : n < 35968
  · exact in_checked_range checked35840 (by omega) (by omega)

  by_cases h35968 : n < 36096
  · exact in_checked_range checked35968 (by omega) (by omega)

  by_cases h36096 : n < 36224
  · exact in_checked_range checked36096 (by omega) (by omega)

  by_cases h36224 : n < 36352
  · exact in_checked_range checked36224 (by omega) (by omega)

  by_cases h36352 : n < 36480
  · exact in_checked_range checked36352 (by omega) (by omega)

  by_cases h36480 : n < 36608
  · exact in_checked_range checked36480 (by omega) (by omega)

  by_cases h36608 : n < 36736
  · exact in_checked_range checked36608 (by omega) (by omega)

  exact in_checked_range checked36736 (by omega) (by omega)
