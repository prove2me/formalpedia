-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock00000
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-25T06:46:56.898679+00:00
-- url     : https://prove2.me/submissions/0b4e97d5-dba9-4616-a15a-02db1f9fdc90

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

set_option maxHeartbeats 0
set_option Elab.async false

private theorem checked0 : pass nodeCheck 0 128 = true := by decide +kernel

private theorem checked128 : pass nodeCheck 128 128 = true := by decide +kernel

private theorem checked256 : pass nodeCheck 256 128 = true := by decide +kernel

private theorem checked384 : pass nodeCheck 384 128 = true := by decide +kernel

private theorem checked512 : pass nodeCheck 512 128 = true := by decide +kernel

private theorem checked640 : pass nodeCheck 640 128 = true := by decide +kernel

private theorem checked768 : pass nodeCheck 768 128 = true := by decide +kernel

private theorem checked896 : pass nodeCheck 896 128 = true := by decide +kernel

private theorem checked1024 : pass nodeCheck 1024 128 = true := by decide +kernel

private theorem checked1152 : pass nodeCheck 1152 128 = true := by decide +kernel

private theorem checked1280 : pass nodeCheck 1280 128 = true := by decide +kernel

private theorem checked1408 : pass nodeCheck 1408 128 = true := by decide +kernel

private theorem checked1536 : pass nodeCheck 1536 128 = true := by decide +kernel

private theorem checked1664 : pass nodeCheck 1664 128 = true := by decide +kernel

private theorem checked1792 : pass nodeCheck 1792 128 = true := by decide +kernel

private theorem checked1920 : pass nodeCheck 1920 128 = true := by decide +kernel


private theorem in_checked_range {a w n : ℕ} (h : pass nodeCheck a w = true)
    (hlo : a ≤ n) (hhi : n < a + w) : nodeCheck n = true := by
  have hm : n - a ∈ List.range w := List.mem_range.mpr (by omega)
  have hh := List.all_eq_true.mp h _ hm
  simpa only [Nat.add_sub_of_le hlo] using hh

theorem solution : ∀ n : ℕ, 0 ≤ n → n < 2048 → nodeCheck n = true := by
  intro n hlo hhi

  by_cases h0 : n < 128
  · exact in_checked_range checked0 (by omega) (by omega)

  by_cases h128 : n < 256
  · exact in_checked_range checked128 (by omega) (by omega)

  by_cases h256 : n < 384
  · exact in_checked_range checked256 (by omega) (by omega)

  by_cases h384 : n < 512
  · exact in_checked_range checked384 (by omega) (by omega)

  by_cases h512 : n < 640
  · exact in_checked_range checked512 (by omega) (by omega)

  by_cases h640 : n < 768
  · exact in_checked_range checked640 (by omega) (by omega)

  by_cases h768 : n < 896
  · exact in_checked_range checked768 (by omega) (by omega)

  by_cases h896 : n < 1024
  · exact in_checked_range checked896 (by omega) (by omega)

  by_cases h1024 : n < 1152
  · exact in_checked_range checked1024 (by omega) (by omega)

  by_cases h1152 : n < 1280
  · exact in_checked_range checked1152 (by omega) (by omega)

  by_cases h1280 : n < 1408
  · exact in_checked_range checked1280 (by omega) (by omega)

  by_cases h1408 : n < 1536
  · exact in_checked_range checked1408 (by omega) (by omega)

  by_cases h1536 : n < 1664
  · exact in_checked_range checked1536 (by omega) (by omega)

  by_cases h1664 : n < 1792
  · exact in_checked_range checked1664 (by omega) (by omega)

  by_cases h1792 : n < 1920
  · exact in_checked_range checked1792 (by omega) (by omega)

  exact in_checked_range checked1920 (by omega) (by omega)
