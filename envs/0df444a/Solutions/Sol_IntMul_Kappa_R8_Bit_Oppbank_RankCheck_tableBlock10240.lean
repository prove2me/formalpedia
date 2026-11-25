-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock10240
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T07:41:30.478797+00:00
-- url     : https://prove2.me/submissions/9e63f782-3008-4bcb-9f22-5d10dd141067

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked10240 : pass nodeFast 10240 128 = true := by decide +kernel

private theorem checked10368 : pass nodeFast 10368 128 = true := by decide +kernel

private theorem checked10496 : pass nodeFast 10496 128 = true := by decide +kernel

private theorem checked10624 : pass nodeFast 10624 128 = true := by decide +kernel

private theorem checked10752 : pass nodeFast 10752 128 = true := by decide +kernel

private theorem checked10880 : pass nodeFast 10880 128 = true := by decide +kernel

private theorem checked11008 : pass nodeFast 11008 128 = true := by decide +kernel

private theorem checked11136 : pass nodeFast 11136 128 = true := by decide +kernel

private theorem checked11264 : pass nodeFast 11264 128 = true := by decide +kernel

private theorem checked11392 : pass nodeFast 11392 128 = true := by decide +kernel

private theorem checked11520 : pass nodeFast 11520 128 = true := by decide +kernel

private theorem checked11648 : pass nodeFast 11648 128 = true := by decide +kernel

private theorem checked11776 : pass nodeFast 11776 128 = true := by decide +kernel

private theorem checked11904 : pass nodeFast 11904 128 = true := by decide +kernel

private theorem checked12032 : pass nodeFast 12032 128 = true := by decide +kernel

private theorem checked12160 : pass nodeFast 12160 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 10240 ≤ n → n < 12288 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h10240 : n < 10368
  · exact in_checked_range checked10240 (by omega) (by omega)

  by_cases h10368 : n < 10496
  · exact in_checked_range checked10368 (by omega) (by omega)

  by_cases h10496 : n < 10624
  · exact in_checked_range checked10496 (by omega) (by omega)

  by_cases h10624 : n < 10752
  · exact in_checked_range checked10624 (by omega) (by omega)

  by_cases h10752 : n < 10880
  · exact in_checked_range checked10752 (by omega) (by omega)

  by_cases h10880 : n < 11008
  · exact in_checked_range checked10880 (by omega) (by omega)

  by_cases h11008 : n < 11136
  · exact in_checked_range checked11008 (by omega) (by omega)

  by_cases h11136 : n < 11264
  · exact in_checked_range checked11136 (by omega) (by omega)

  by_cases h11264 : n < 11392
  · exact in_checked_range checked11264 (by omega) (by omega)

  by_cases h11392 : n < 11520
  · exact in_checked_range checked11392 (by omega) (by omega)

  by_cases h11520 : n < 11648
  · exact in_checked_range checked11520 (by omega) (by omega)

  by_cases h11648 : n < 11776
  · exact in_checked_range checked11648 (by omega) (by omega)

  by_cases h11776 : n < 11904
  · exact in_checked_range checked11776 (by omega) (by omega)

  by_cases h11904 : n < 12032
  · exact in_checked_range checked11904 (by omega) (by omega)

  by_cases h12032 : n < 12160
  · exact in_checked_range checked12032 (by omega) (by omega)

  exact in_checked_range checked12160 (by omega) (by omega)
