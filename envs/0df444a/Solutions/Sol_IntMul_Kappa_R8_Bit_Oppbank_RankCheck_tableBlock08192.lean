-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock08192
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T08:04:52.969887+00:00
-- url     : https://prove2.me/submissions/ce444631-c38e-41d0-8354-e744817dfdc4

import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked8192 : pass nodeFast 8192 128 = true := by decide +kernel

private theorem checked8320 : pass nodeFast 8320 128 = true := by decide +kernel

private theorem checked8448 : pass nodeFast 8448 128 = true := by decide +kernel

private theorem checked8576 : pass nodeFast 8576 128 = true := by decide +kernel

private theorem checked8704 : pass nodeFast 8704 128 = true := by decide +kernel

private theorem checked8832 : pass nodeFast 8832 128 = true := by decide +kernel

private theorem checked8960 : pass nodeFast 8960 128 = true := by decide +kernel

private theorem checked9088 : pass nodeFast 9088 128 = true := by decide +kernel

private theorem checked9216 : pass nodeFast 9216 128 = true := by decide +kernel

private theorem checked9344 : pass nodeFast 9344 128 = true := by decide +kernel

private theorem checked9472 : pass nodeFast 9472 128 = true := by decide +kernel

private theorem checked9600 : pass nodeFast 9600 128 = true := by decide +kernel

private theorem checked9728 : pass nodeFast 9728 128 = true := by decide +kernel

private theorem checked9856 : pass nodeFast 9856 128 = true := by decide +kernel

private theorem checked9984 : pass nodeFast 9984 128 = true := by decide +kernel

private theorem checked10112 : pass nodeFast 10112 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeFast a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  exact nodeFast_sound (by simpa only [Nat.add_sub_of_le hlo] using hh)

theorem solution : ∀ n : ℕ, 8192 ≤ n → n < 10240 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h8192 : n < 8320
  · exact in_checked_range checked8192 (by omega) (by omega)

  by_cases h8320 : n < 8448
  · exact in_checked_range checked8320 (by omega) (by omega)

  by_cases h8448 : n < 8576
  · exact in_checked_range checked8448 (by omega) (by omega)

  by_cases h8576 : n < 8704
  · exact in_checked_range checked8576 (by omega) (by omega)

  by_cases h8704 : n < 8832
  · exact in_checked_range checked8704 (by omega) (by omega)

  by_cases h8832 : n < 8960
  · exact in_checked_range checked8832 (by omega) (by omega)

  by_cases h8960 : n < 9088
  · exact in_checked_range checked8960 (by omega) (by omega)

  by_cases h9088 : n < 9216
  · exact in_checked_range checked9088 (by omega) (by omega)

  by_cases h9216 : n < 9344
  · exact in_checked_range checked9216 (by omega) (by omega)

  by_cases h9344 : n < 9472
  · exact in_checked_range checked9344 (by omega) (by omega)

  by_cases h9472 : n < 9600
  · exact in_checked_range checked9472 (by omega) (by omega)

  by_cases h9600 : n < 9728
  · exact in_checked_range checked9600 (by omega) (by omega)

  by_cases h9728 : n < 9856
  · exact in_checked_range checked9728 (by omega) (by omega)

  by_cases h9856 : n < 9984
  · exact in_checked_range checked9856 (by omega) (by omega)

  by_cases h9984 : n < 10112
  · exact in_checked_range checked9984 (by omega) (by omega)

  exact in_checked_range checked10112 (by omega) (by omega)
