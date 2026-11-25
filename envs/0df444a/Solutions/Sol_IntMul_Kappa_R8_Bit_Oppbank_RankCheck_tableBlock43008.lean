-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock43008
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:40:45.246879+00:00
-- url     : https://prove2.me/submissions/3e402dad-6cce-44c5-a755-6341cc58e3cf

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked43008 : pass nodeFast 43008 128 = true := by decide +kernel

private theorem checked43136 : pass nodeFast 43136 128 = true := by decide +kernel

private theorem checked43264 : pass nodeFast 43264 128 = true := by decide +kernel

private theorem checked43392 : pass nodeFast 43392 128 = true := by decide +kernel

private theorem checked43520 : pass nodeFast 43520 128 = true := by decide +kernel

private theorem checked43648 : pass nodeFast 43648 128 = true := by decide +kernel

private theorem checked43776 : pass nodeFast 43776 128 = true := by decide +kernel

private theorem checked43904 : pass nodeFast 43904 128 = true := by decide +kernel

private theorem checked44032 : pass nodeFast 44032 128 = true := by decide +kernel

private theorem checked44160 : pass nodeFast 44160 128 = true := by decide +kernel

private theorem checked44288 : pass nodeFast 44288 128 = true := by decide +kernel

private theorem checked44416 : pass nodeFast 44416 128 = true := by decide +kernel

private theorem checked44544 : pass nodeFast 44544 128 = true := by decide +kernel

private theorem checked44672 : pass nodeFast 44672 128 = true := by decide +kernel

private theorem checked44800 : pass nodeFast 44800 128 = true := by decide +kernel

private theorem checked44928 : pass nodeFast 44928 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 43008 ≤ n → n < 45056 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h43008 : n < 43136
  · exact in_checked_range checked43008 (by omega) (by omega)

  by_cases h43136 : n < 43264
  · exact in_checked_range checked43136 (by omega) (by omega)

  by_cases h43264 : n < 43392
  · exact in_checked_range checked43264 (by omega) (by omega)

  by_cases h43392 : n < 43520
  · exact in_checked_range checked43392 (by omega) (by omega)

  by_cases h43520 : n < 43648
  · exact in_checked_range checked43520 (by omega) (by omega)

  by_cases h43648 : n < 43776
  · exact in_checked_range checked43648 (by omega) (by omega)

  by_cases h43776 : n < 43904
  · exact in_checked_range checked43776 (by omega) (by omega)

  by_cases h43904 : n < 44032
  · exact in_checked_range checked43904 (by omega) (by omega)

  by_cases h44032 : n < 44160
  · exact in_checked_range checked44032 (by omega) (by omega)

  by_cases h44160 : n < 44288
  · exact in_checked_range checked44160 (by omega) (by omega)

  by_cases h44288 : n < 44416
  · exact in_checked_range checked44288 (by omega) (by omega)

  by_cases h44416 : n < 44544
  · exact in_checked_range checked44416 (by omega) (by omega)

  by_cases h44544 : n < 44672
  · exact in_checked_range checked44544 (by omega) (by omega)

  by_cases h44672 : n < 44800
  · exact in_checked_range checked44672 (by omega) (by omega)

  by_cases h44800 : n < 44928
  · exact in_checked_range checked44800 (by omega) (by omega)

  exact in_checked_range checked44928 (by omega) (by omega)
