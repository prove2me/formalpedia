-- Prove2me | solution 1 for OAI.SharpPlanar.halfGap_segment_lower
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T12:40:14.467976+00:00
-- url     : https://prove2.me/submissions/f20851df-6cef-4db6-bd0a-958f118a6b74

import Mathlib

theorem solution {v m y s N : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hm : N ≤ m) (hy : N ≤ m + y) (hs : s ∈ Set.uIcc m (m + y * v)) : N ≤ s := by
  have hv0 : 0 ≤ v := hv.1
  have hv1 : v ≤ 1 := hv.2
  have hN2 : N ≤ m + y * v := by
    rcases le_or_gt 0 y with hy0 | hy0
    · nlinarith [mul_nonneg hy0 hv0]
    · have hyv : m + y ≤ m + y * v := by
        have h := mul_le_mul_of_nonpos_left hv1 (le_of_lt hy0)
        linarith
      linarith
  rw [Set.mem_uIcc] at hs
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
